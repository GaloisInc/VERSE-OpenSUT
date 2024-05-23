use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::mem;
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Child};
use std::thread;
use std::time::Duration;
use log::trace;
use nix;
use nix::unistd::Pid;
use nix::sys::wait::{WaitStatus, WaitPidFlag};
use toml;
use crate::config::{Config, Mode};

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

fn build_commands(processes: &[config::Process]) -> Commands {
    let mut cmds = Commands::default();
    for process in processes {
        match *process {
            config::Process::Shell(ref shell) => {
                let mut cmd = Command::new("/bin/sh");
                cmd.args(&["-c", &shell.command]);
                cmds.commands.push(cmd);
            },
            config::Process::Vm(ref vm) => {
                build_vm_command(vm, &mut cmds);
            },
        }
    }
    cmds
}

fn needs_escaping_for_qemu(arg: &str) -> bool {
    arg.contains(&[',', '=', ':'])
}

fn build_vm_command(vm: &config::VmProcess, cmds: &mut Commands) {
    let config::VmProcess {
        ref kernel, ref initrd, ref append,
        ram_mb, kvm,
        ref disk, ref net, ref fs_9p, ref gpio,
    } = *vm;

    let mut vm_cmd = Command::new("qemu-system-aarch64");

    // Basic machine configuration
    vm_cmd.args(&["-M", "virt"]);
    vm_cmd.args(&["-smp", "4"]);
    vm_cmd.args(&["-m", &format!("{}", ram_mb)]);
    vm_cmd.args(&["-nographic"]);

    // KVM
    if kvm {
        vm_cmd.args(&["-cpu", "host"]);
        vm_cmd.args(&["-enable-kvm"]);
    } else {
        vm_cmd.args(&["-cpu", "cortex-a72"]);
        vm_cmd.args(&["-machine", "virtualization=true"]);
        vm_cmd.args(&["-machine", "virt,gic-version=3"]);
    }

    // Non-configurable devices
    vm_cmd.args(&["-device", "virtio-scsi-pci,id=scsi0"]);
    vm_cmd.args(&["-object", "rng-random,filename=/dev/urandom,id=rng0"]);
    vm_cmd.args(&["-device", "virtio-rng-pci,rng=rng0"]);

    // Kernel and related flags
    vm_cmd.args(&["-kernel", &kernel]);
    if let Some(ref initrd) = initrd {
        vm_cmd.args(&["-initrd", &initrd]);
    }
    if append.len() > 0 {
        vm_cmd.args(&["-append", &append]);
    }

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
        vm_cmd.args(&["-drive", &format!("if=virtio,format={},file={}", d.format, d.path)]);
    }

    let config::VmNet { ref port_forward } = *net;
    let mut netdev_str = format!("user,id=net0");
    for pf in port_forward.values() {
        write!(netdev_str, ",hostfwd=tcp:127.0.0.1:{}-:{}", pf.outer_port, pf.inner_port)
            .unwrap();
    }
    vm_cmd.args(&["-device", "virtio-net-pci,netdev=net0"]);
    vm_cmd.args(&["-netdev", &netdev_str]);

    for (name, fs) in fs_9p {
        assert!(!needs_escaping_for_qemu(name),
            "unsupported character in 9p name {:?}", name);
        assert!(!needs_escaping_for_qemu(&fs.path),
            "unsupported character in 9p {} path: {:?}", name, fs.path);
        vm_cmd.args(&["-fsdev",
            &format!("local,id=fs_9p__{},path={},security_model=mapped-xattr", name, fs.path)]);
        vm_cmd.args(&["-device",
            &format!("virtio-9p-pci,fsdev=fs_9p__{},mount_tag={}", name, name)]);
    }

    if gpio.len() > 0 {
        vm_cmd.args(&["-object",
            &format!("memory-backend-file,id=mem,size={}M,mem_path=/dev/shm,share=on", ram_mb)]);
        vm_cmd.args(&["-numa", "node,memdev=mem"]);
    }
    for (name, g) in gpio {
        todo!();
    }

    cmds.commands.push(vm_cmd);
}


pub fn run_manage(cfg: &Config) -> io::Result<()> {
    let mut children = ManagedProcesses::new();

    let cmds = build_commands(&cfg.process);

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

    let mut cmds = build_commands(&cfg.process);
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


pub fn runner_main(config_path: impl AsRef<Path>) {
    let config_str = fs::read_to_string(config_path).unwrap();
    let cfg: Config = toml::from_str(&config_str).unwrap();

    trace!("parsed config = {:?}", cfg);

    match cfg.mode {
        Mode::Manage => run_manage(&cfg).unwrap(),
        Mode::Exec => run_exec(&cfg).unwrap(),
    }
}
