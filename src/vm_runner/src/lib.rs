use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{self, Read};
use std::mem;
use std::os::raw::c_int;
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Child};
use std::thread;
use std::time::Duration;
use log::trace;
use nix;
use nix::mount::MsFlags;
use nix::unistd::Pid;
use nix::sys::wait::{WaitStatus, WaitPidFlag};
use sha2::{Sha256, Digest};
use shlex::Shlex;
use toml;
use crate::config::{Config, Mode, Paths, VmSerial};

pub mod config;


/// Helper for cleaning up child processes on drop.  The caller is responsible for adding each
/// child as soon as it's spawned, and for removing children after `wait` indicates that they've
/// terminated.  If an error occurs, the `ManagedProcesses` object will be dropped, and any child
/// processes currently registered with it will be killed.
struct ManagedProcesses {
    children: HashMap<u32, Child>,
}

impl ManagedProcesses {
    pub fn new() -> ManagedProcesses {
        ManagedProcesses {
            children: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.children.len()
    }

    pub fn add(&mut self, child: Child) {
        let pid = child.id();
        self.children.insert(pid, child);
    }

    pub fn remove(&mut self, pid: u32) -> Option<Child> {
        self.children.remove(&pid)
    }
}

impl Drop for ManagedProcesses {
    fn drop(&mut self) {
        for (&pid, child) in &mut self.children {
            let result = child.kill();
            match result {
                Ok(()) => {},
                Err(e) => {
                    eprintln!("failed to kill child {}: {}", pid, e);
                    // Continue trying to kill remaining children.
                },
            }
        }

        for (pid, mut child) in mem::take(&mut self.children) {
            let result = child.wait();
            match result {
                Ok(_) => {},
                Err(e) => {
                    eprintln!("failed to wait for child {}: {}", pid, e);
                    // Continue waiting on remaining children.
                },
            }
        }
    }
}


#[derive(Debug, Default)]
struct Commands {
    /// Start these processes early, before the ones in `commands`.
    early_commands: Vec<Command>,
    commands: Vec<Command>,
}

fn build_commands(paths: &Paths, processes: &[config::Process]) -> Commands {
    let mut cmds = Commands::default();
    for process in processes {
        match *process {
            config::Process::Shell(ref shell) => {
                let mut cmd = Command::new("/bin/sh");
                cmd.current_dir(&shell.cwd);
                cmd.args(&["-c", &shell.command]);
                cmds.commands.push(cmd);
            },
            config::Process::Vm(ref vm) => {
                build_vm_command(paths, vm, &mut cmds);
            },
        }
    }
    cmds
}

fn needs_escaping_for_qemu(path: impl AsRef<Path>) -> bool {
    let s = match path.as_ref().to_str() {
        Some(x) => x,
        // If the path isn't valid UTF-8, we can't examine it, so conservatively assume it might
        // need escaping.
        None => return true,
    };
    s.contains(&[',', '=', ':'])
}

fn build_vm_command(paths: &Paths, vm: &config::VmProcess, cmds: &mut Commands) {
    let config::VmProcess {
        ref kernel, ref initrd, ref append,
        ram_mb, kvm,
        ref disk, ref net, ref fs_9p, ref serial, ref gpio,
    } = *vm;

    let mut vm_cmd = Command::new(paths.qemu_system_aarch64());

    macro_rules! args {
        ($l:literal $($rest:tt)*) => {{
            vm_cmd.arg($l);
            args!($($rest)*);
        }};
        (($e:expr) $($rest:tt)*) => {{
            vm_cmd.arg($e);
            args!($($rest)*);
        }};
        ($i:ident $($rest:tt)*) => {{
            vm_cmd.arg($i);
            args!($($rest)*);
        }};
        () => { () };
    }

    // Basic machine configuration
    args!("-M" "virt");
    args!("-smp" "4");
    args!("-m" (format!("{}", ram_mb)));

    // KVM
    if kvm {
        args!("-cpu" "host");
        args!("-enable-kvm");
    } else {
        args!("-cpu" "cortex-a72");
        args!("-machine" "virtualization=true");
        args!("-machine" "virt,gic-version=3");
    }

    // Non-configurable devices
    args!("-device" "virtio-scsi-pci,id=scsi0");
    args!("-object" "rng-random,filename=/dev/urandom,id=rng0");
    args!("-device" "virtio-rng-pci,rng=rng0");
    args!("-display" "none");

    // Kernel and related flags
    args!("-kernel" kernel);
    if let Some(ref initrd) = initrd {
        args!("-initrd" initrd);
    }
    if append.len() > 0 {
        args!("-append" append);
    }


    // Serial ports

    // Set up a character device for stdio and use it for the QEMU monitor.
    args!("-chardev" "stdio,mux=on,id=char_stdio,signal=off");
    args!("-mon" "chardev=char_stdio,mode=readline");

    /// Handle serial port configuration.  This will add `-chardev` definitions to `cmd` if needed,
    /// and will return the `chardev` name for use with `-serial` or `-device`.
    ///
    /// `name` is the name of the device being configured, which is used to generate unique
    /// `chardev` names and for error reporting.
    fn handle_serial(vm_cmd: &mut Command, name: &str, s: &VmSerial) -> String {
        match *s {
            VmSerial::Stdio => "char_stdio".to_string(),
            VmSerial::Passthrough(ref ps) => {
                assert!(!needs_escaping_for_qemu(&ps.device),
                    "unsupported character in serial {} device: {:?}", name, ps.device);
                let device = ps.device.to_str().unwrap();
                vm_cmd.args(&["-chardev",
                    &format!("serial,id=char_{},path={}", name, device)]);
                format!("char_{}", name)
            },
            VmSerial::Unix(ref us) => {
                assert!(!needs_escaping_for_qemu(&us.path),
                    "unsupported character in serial {} path: {:?}", name, us.path);
                let path = us.path.to_str().unwrap();
                vm_cmd.args(&["-chardev",
                    &format!("socket,id=char_{},path={},server=on,wait=off", name, path)]);
                format!("char_{}", name)
            },
        }
    }

    let serial_range;
    const DEFAULT_SERIAL_NAME: &str = "ttyAMA0";
    if let Some(s) = serial.get(DEFAULT_SERIAL_NAME) {
        let chardev = handle_serial(&mut vm_cmd, DEFAULT_SERIAL_NAME, s);
        args!("-serial" (format!("chardev:{}", chardev)));
        serial_range = 0 .. serial.len() - 1;
    } else {
        // Default behavior: connect `ttyAMA0` to stdio
        args!("-serial" "chardev:char_stdio");
        serial_range = 0 .. serial.len();
    }

    // A `virtio-serial-pci` device provides the QEMU-internal `virtio-serial-bus`, which later
    // `virtconsole` devices attach to.
    args!("-device" "virtio-serial-pci");
    // A single `virtio-serial-pci` provides 8 ports.
    const MAX_SERIAL_DEVICES: usize = 8;
    assert!(serial_range.end - serial_range.start <= MAX_SERIAL_DEVICES,
        "too many serial devices (max = {})", MAX_SERIAL_DEVICES);

    for i in serial_range {
        let name = format!("hvc{}", i);
        let s = serial.get(&name)
            .unwrap_or_else(|| panic!("non-contiguous serial port definitions: missing {}", name));
        let chardev = handle_serial(&mut vm_cmd, &name, s);
        args!("-device" (format!("virtconsole,chardev={}", chardev)));
    }


    // Disks
    for i in 0 .. disk.len() {
        let i = u8::try_from(i).unwrap();
        let letter = (b'a' + i) as char;
        let name = format!("vd{}", letter);
        let d = disk.get(&name)
            .unwrap_or_else(|| panic!("non-contiguous disk definitions: missing {}", name));
        // Forbid characters that require escaping in QEMU device arguments.
        assert!(!needs_escaping_for_qemu(&d.path),
            "unsupported character in disk {} path: {:?}", name, d.path);
        assert!(["qcow2", "raw"].contains(&(&d.format as &str)),
            "unsupported format for disk {}: {:?}", name, d.format);
        let path = d.path.to_str().unwrap();
        let read_only = if d.read_only { "on" } else { "off" };
        args!("-drive"
            (format!("if=virtio,format={},file={},read-only={}", d.format, path, read_only)));
    }

    let config::VmNet { ref port_forward } = *net;
    let mut netdev_str = format!("user,id=net0");
    for pf in port_forward.values() {
        write!(netdev_str, ",hostfwd=tcp:127.0.0.1:{}-:{}", pf.outer_port, pf.inner_port)
            .unwrap();
    }
    args!("-device" "virtio-net-pci,netdev=net0");
    args!("-netdev" netdev_str);

    for (name, fs) in fs_9p {
        assert!(!needs_escaping_for_qemu(name),
            "unsupported character in 9p name {:?}", name);
        assert!(!needs_escaping_for_qemu(&fs.path),
            "unsupported character in 9p {} path: {:?}", name, fs.path);
        let path = fs.path.to_str().unwrap();
        args!("-fsdev"
            (format!("local,id=fs_9p__{},path={},security_model=mapped-xattr", name, path)));
        args!("-device"
            (format!("virtio-9p-pci,fsdev=fs_9p__{},mount_tag={}", name, name)));
    }

    if gpio.len() > 0 {
        args!("-object"
            (format!("memory-backend-file,id=mem,size={}M,mem_path=/dev/shm,share=on", ram_mb)));
        args!("-numa" "node,memdev=mem");
    }
    for (_name, _g) in gpio {
        // TODO: add vhost-device-gpio as an early_command, and add a -device flag to vm_cmd
        todo!("gpio devices are not yet implemented");
    }

    cmds.commands.push(vm_cmd);
}


pub fn run_manage(cfg: &Config) -> io::Result<()> {
    let mut children = ManagedProcesses::new();

    let cmds = build_commands(&cfg.paths, &cfg.process);

    if cmds.early_commands.len() > 0 {
        for mut cmd in cmds.early_commands {
            trace!("spawn (early): {:?}", cmd);
            let child = cmd.spawn()?;
            trace!("spawned pid = {}", child.id());
            children.add(child);
        }

        // Give daemons time to start up and open their sockets.
        // TODO: Use a systemd-notify like protocol to wait for daemon startup.
        thread::sleep(Duration::from_millis(200));
    }

    for mut cmd in cmds.commands {
        trace!("spawn: {:?}", cmd);
        let child = cmd.spawn()?;
        trace!("spawned pid = {}", child.id());
        children.add(child);
    }

    // Await all children.  If any child returns nonzero, kill all other children.
    while children.len() > 0 {
        trace!("waitpid...");
        let status = nix::sys::wait::waitid(nix::sys::wait::Id::All, WaitPidFlag::WEXITED)?;
        trace!("waitpid returned {:?}", status);
        let mut remove_child = |pid: Pid| {
            let pid = u32::try_from(pid.as_raw()).unwrap();
            children.remove(pid);
        };
        match status {
            WaitStatus::Exited(pid, exit_code) => {
                if exit_code == 0 {
                    // Normal exit.  Just remove the child.
                    remove_child(pid);
                } else {
                    // Abnormal exit.
                    remove_child(pid);
                    panic!("process {} exited unexpectedly with code {}", pid, exit_code);
                }
            },
            WaitStatus::Signaled(pid, signal, _) => {
                // Killed by a signal.
                remove_child(pid);
                panic!("process {} was killed unexpectedly by signal {:?}", pid, signal);
            },
            WaitStatus::Stopped(pid, signal) => {
                // Process suspended by SIGSTOP or similar.  We should never receive this event,
                // since we don't include `WUNTRACED`/`WSTOPPED` in the `waidpid` call above.
                //
                // The child is still alive, so don't remove it from `children`.
                panic!("impossible: waitpid reported that {} stopped due to signal {:?}, \
                    but we did not request such events", pid, signal);
            },
            WaitStatus::Continued(pid) => {
                // Process continued due to SIGCONT or similar.  We should never receive this
                // event, since we don't include `WCONTINUED` in the `waidpid` call above.
                //
                // The child is still alive, so don't remove it from `children`.
                panic!("impossible: waitpid reported that {} continued due to a signal, \
                    but we did not request such events", pid);
            },
            WaitStatus::PtraceEvent(pid, _, event) => {
                // Stopped by ptrace.  This can happen when the child invokes `PTRACE_TRACEME`.
                //
                // The child is still alive, so don't remove it from `children`.
                panic!("process {} unexpectedly stopped with ptrace event {}", pid, event);
            },
            WaitStatus::PtraceSyscall(pid) => {
                // Stopped by ptrace due to a syscall.  We should never receive this event, since
                // we don't enable syscall tracing on any children.
                //
                // The child is still alive, so don't remove it from `children`.
                panic!("impossible: waitpid reported that {} stopped due to a ptrace syscall, \
                    but we did not enable syscall tracing", pid);
            },
            WaitStatus::StillAlive => {
                // No state change; process is still alive.  We should never receive this event,
                // since we don't include `WNOHANG` in the `waidpid` call above.
                panic!("impossible: waitpid reported no changes, \
                    but we expected it to block until a change occurred");
            },
        }
    }

    Ok(())
}

pub fn run_exec(cfg: &Config) -> io::Result<()> {
    assert!(cfg.process.len() == 1,
        "config error: `mode = 'exec'` requires exactly one entry in `processes`");

    let mut cmds = build_commands(&cfg.paths, &cfg.process);
    assert!(cmds.commands.len() == 1,
        "impossible: one `Process` produced multiple main `Command`s");
    assert!(cmds.early_commands.len() == 0,
        "process requires running helpers, which `mode = 'exec'` does not support");

    let mut cmd = cmds.commands.pop().unwrap();
    trace!("exec: {:?}", cmd);
    let err = cmd.exec();
    trace!("exec error: {}", err);
    Err(err)
}


fn hash_file(path: impl AsRef<Path>) -> io::Result<[u8; 32]> {
    let path = path.as_ref();
    trace!("hash_file: opening {:?}", path);
    let mut f = File::open(path)?;
    let mut buf = vec![0; 64 * 1024];
    let mut hasher = Sha256::new();
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(hasher.finalize().into())
}

fn nix_write_all(fd: c_int, data: &[u8]) -> io::Result<usize> {
    let mut sent = 0;
    while sent < data.len() {
        let n = nix::unistd::write(fd, &data[sent..])?;
        if n == 0 {
            break;
        }
        sent += n;
    }
    Ok(sent)
}


pub fn runner_main(config_path: impl AsRef<Path>) {
    let config_path = config_path.as_ref();
    let config_str = fs::read_to_string(config_path).unwrap();
    let mut cfg: Config = toml::from_str(&config_str).unwrap();
    cfg.resolve_relative_paths(config_path.parent().unwrap());

    trace!("parsed config = {:?}", cfg);

    match cfg.mode {
        Mode::Manage => run_manage(&cfg).unwrap(),
        Mode::Exec => run_exec(&cfg).unwrap(),
    }
}


pub fn boot_main() {
    // Find the device containing the application partition.
    let cmdline = fs::read_to_string("/proc/cmdline").unwrap();
    let mut app_device = None;
    for arg in Shlex::new(&cmdline) {
        let (key, value) = match arg.split_once('=') {
            Some(x) => x,
            None => continue,
        };
        if key != "opensut.app_device" {
            continue;
        }
        app_device = Some(value.to_owned());
    }
    let app_device = app_device
        .unwrap_or_else(|| panic!("missing opensut.app_device in kernel command line"));

    eprintln!("trusted boot fd = {:?}", env::var("VERSE_TRUSTED_BOOT_FD"));
    if let Ok(fd_str) = env::var("VERSE_TRUSTED_BOOT_FD") {
        // Open the device and mix its hash into the secure boot measurement.
        let hash = hash_file(&app_device).unwrap();
        let fd = fd_str.parse().unwrap();
        let mut message = [0; 1 + 2 + 32];
        message[0] = 1; // `measure` command
        message[1..3].copy_from_slice(&32_u16.to_le_bytes());   // Input size
        message[3..].copy_from_slice(&hash);
        let n = nix_write_all(fd, &message).unwrap();
        assert_eq!(n, message.len());
    }

    // Mount the application device
    const APP_MOUNT_POINT: &str = "/opt/opensut/app";
    fs::create_dir_all(APP_MOUNT_POINT).unwrap();
    nix::mount::mount(
        Some(&app_device as &str),
        APP_MOUNT_POINT,
        Some("squashfs"),
        MsFlags::MS_RDONLY,
        None::<&str>,   // No filesystem-specific data
    ).unwrap();

    // Start the runner using the application's config file
    runner_main(Path::new(APP_MOUNT_POINT).join("runner.toml"));
}
