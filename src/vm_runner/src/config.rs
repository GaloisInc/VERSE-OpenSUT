use std::collections::HashMap;
use std::path::{Path, PathBuf};
use indexmap::IndexMap;
use log::trace;
use serde::{Serialize, Deserialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub mode: Mode,
    #[serde(default)]
    pub process: Vec<Process>,
    #[serde(default)]
    pub paths: Paths,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Mode {
    /// Manage multiple processes running concurrently.  Any number of processes is permitted.  All
    /// processes will be started, and the runner will wait for all of them to exit.  If a process
    /// exits unsuccessfully, all other processes will be terminated.
    Manage,
    /// `exec` a single command.  There must be exactly one process in the config file.
    Exec,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Paths {
    pub qemu_system_aarch64: Option<PathBuf>,
    /// This field is mainly for internal use, but it can be set in the config file to override
    /// QEMU version detection.
    pub qemu_system_aarch64_version: Option<Vec<u8>>,
}

impl Paths {
    pub fn qemu_system_aarch64(&self) -> &Path {
        self.qemu_system_aarch64.as_ref()
            .map_or(Path::new("qemu-system-aarch64"), |x| x)
    }

    pub fn qemu_system_aarch64_version(&self) -> &[u8] {
        self.qemu_system_aarch64_version.as_ref()
            .expect("qemu_system_aarch64_version should be auto-detected after config parsing \
                if any `Process` might need it")
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Process {
    Shell(ShellProcess),
    Vm(VmProcess),
}

/// Run a shell command.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ShellProcess {
    pub command: String,
    /// Directory to use as the current directory when running `command`.  By default, this is the
    /// directory containing the config file, so any paths in `command` are interpreted relative to
    /// the config directory.
    #[serde(default)]
    pub cwd: PathBuf,
}

/// Spawn a VM.
///
/// This could instead be done using a `ShellProcess` that invokes QEMU, but using `type = "vm"`
/// handles the most common device options automatically.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VmProcess {
    pub kernel: PathBuf,
    pub initrd: Option<PathBuf>,
    #[serde(default)]
    pub append: String,

    #[serde(default = "const_u32::<1024>")]
    pub ram_mb: u32,

    /// If set, use KVM.  Otherwise, run emulation with no hardware support.
    ///
    /// Using KVM requires access to the `/dev/kvm` device.
    #[serde(default = "const_bool::<true>")]
    pub kvm: bool,

    /// Disk definitions.  Devices must be named sequentially as `vda`, `vdb`, and so on.  They
    /// will be presented to the guest in name order, so `vda` will appear as `/dev/vda`, `vdb` as
    /// `/dev/vdb`, and so on.
    ///
    /// The disks we present to the guest will be sequentially named starting with `/dev/vda`.
    /// Requiring the user to also name their config file entries sequentially means lets us ensure
    /// that there's a correspondence between the names in the config file and the device names
    /// within the guest.
    #[serde(default)]
    pub disk: HashMap<String, VmDisk>,
    #[serde(default)]
    pub net: VmNet,
    /// 9p filesystem definitions.  The key will be used as the "mount tag", which must be passed
    /// to `mount` in the guest to mount the filesystem.
    #[serde(default, rename = "9p")]
    pub fs_9p: HashMap<String, Vm9P>,
    /// Serial port / UART definitions.  Devices must be named sequentially as `hvc0`,
    /// `hvc1`, and so on.  They will be presented to the guest in name order, so `hvc0` will
    /// appear as `/dev/hvc0`, `hvc1` as `/dev/hvc1`, and so on.
    ///
    /// In addition, the default console can be configured by providing an entry named `ttyAMA0`.
    /// Without such an entry, `ttyAMA0` will be automatically connected to stdio.
    #[serde(default)]
    pub serial: IndexMap<String, VmSerial>,
    /// GPIO device definitions.  Devices are added in order; the first one listed in the config
    /// file will be `/dev/gpiochip1`, the second will be `/dev/gpiochip2`, and so on.  (Note that
    /// the guest will also have a `gpiochip0` provided automatically by QEMU.)
    #[serde(default)]
    pub gpio: IndexMap<String, VmGpio>,
}

fn const_bool<const B: bool>() -> bool {
    B
}

fn const_u32<const N: u32>() -> u32 {
    N
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VmDisk {
    pub format: String,
    pub path: PathBuf,
    #[serde(default = "const_bool::<false>")]
    pub read_only: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VmNet {
    #[serde(default)]
    pub port_forward: HashMap<String, PortForward>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PortForward {
    pub outer_port: u16,
    pub inner_port: u16,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vm9P {
    pub path: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum VmSerial {
    /// Connect the serial port in the guest to stdin/stdout on the host.
    Stdio,
    /// Pass through one of the host's serial ports to the guest.
    Passthrough(PassthroughSerial),
    /// Listen for a Unix socket connection on the host, and connect it to the serial port in the
    /// guest.
    Unix(UnixSerial),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PassthroughSerial {
    pub device: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UnixSerial {
    pub path: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum VmGpio {
    External,
    Passthrough(PassthroughGpio),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PassthroughGpio {
    pub device: PathBuf,
}


fn resolve_relative_path(path: &mut PathBuf, base: &Path) {
    let new = base.join(&*path);
    trace!("resolve_relative_path: {:?} -> {:?}", path, new);
    *path = new;
    //*path = base.join(&*path);
}

fn resolve_relative_path_if_contains_slash(path: &mut PathBuf, base: &Path) {
    // `Path::parent` docs say that it "returns `Some("")` for relative paths with one component".
    if path.parent() == Some(Path::new("")) {
        // Does not contain a slash.
        return;
    }
    resolve_relative_path(path, base);
}

impl Config {
    /// Resolve any relative paths within `self` relative to `base`.
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let Config { ref mut paths, mode: _, ref mut process } = *self;
        paths.resolve_relative_paths(base);
        for p in process {
            p.resolve_relative_paths(base);
        }
    }
}

impl Paths {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let Paths { ref mut qemu_system_aarch64, qemu_system_aarch64_version: _ } = *self;
        if let Some(ref mut path) = qemu_system_aarch64 {
            resolve_relative_path_if_contains_slash(path, base);
        }
    }
}

impl Process {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        match *self {
            Process::Shell(ref mut sp) => sp.resolve_relative_paths(base),
            Process::Vm(ref mut vp) => vp.resolve_relative_paths(base),
        }
    }
}

impl ShellProcess {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let ShellProcess { command: _, ref mut cwd } = *self;
        resolve_relative_path(cwd, base);
    }
}

impl VmProcess {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let VmProcess {
            ref mut kernel, ref mut initrd, append: _,
            ram_mb: _, kvm: _,
            ref mut disk, net: _, ref mut fs_9p, ref mut serial, ref mut gpio,
        } = *self;

        resolve_relative_path(kernel, base);
        if let Some(ref mut initrd) = *initrd {
            resolve_relative_path(initrd, base);
        }

        for x in disk.values_mut() {
            x.resolve_relative_paths(base);
        }
        for x in fs_9p.values_mut() {
            x.resolve_relative_paths(base);
        }
        for x in serial.values_mut() {
            x.resolve_relative_paths(base);
        }
        for x in gpio.values_mut() {
            x.resolve_relative_paths(base);
        }
    }
}

impl VmDisk {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let VmDisk { format: _, ref mut path, read_only: _ } = *self;
        resolve_relative_path(path, base);
    }
}

impl Vm9P {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let Vm9P { ref mut path } = *self;
        resolve_relative_path(path, base);
    }
}

impl VmSerial {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        match *self {
            VmSerial::Stdio => {},
            VmSerial::Passthrough(ref mut ps) => ps.resolve_relative_paths(base),
            VmSerial::Unix(ref mut us) => us.resolve_relative_paths(base),
        }
    }
}

impl PassthroughSerial {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let PassthroughSerial { ref mut device } = *self;
        resolve_relative_path(device, base);
    }
}

impl UnixSerial {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let UnixSerial { ref mut path } = *self;
        resolve_relative_path(path, base);
    }
}

impl VmGpio {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        match *self {
            VmGpio::External => {},
            VmGpio::Passthrough(ref mut ps) => ps.resolve_relative_paths(base),
        }
    }
}

impl PassthroughGpio {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let PassthroughGpio { ref mut device } = *self;
        resolve_relative_path(device, base);
    }
}
