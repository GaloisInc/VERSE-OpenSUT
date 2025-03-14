use std::collections::HashMap;
use std::path::{Path, PathBuf};
use indexmap::IndexMap;
use log::trace;
use serde::{Serialize, Deserialize, Deserializer};

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
    pub vhost_device_gpio: Option<PathBuf>,
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

    pub fn vhost_device_gpio(&self) -> &Path {
        self.vhost_device_gpio.as_ref()
            .map_or(Path::new("vhost-device-gpio"), |x| x)
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
    pub net: IndexMap<String, VmNet>,
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
    /// Disk image format.  Currently `vm_runner` allows only "qcow2" and "raw" formats.  See
    /// `qemu-img --help` for a list of all formats supported by QEMU.
    pub format: String,
    /// Path to the disk image.
    pub path: PathBuf,
    /// If set, QEMU treats the disk image as read-only.  The VM will not be able to write to the
    /// corresponding virtual block device.
    #[serde(default = "const_bool::<false>")]
    pub read_only: bool,
    /// If set, QEMU uses a temporary snapshot of the disk image instead of using it directly.  The
    /// VM will be able to write to the virtual block device as normal, but its writes will be
    /// discarded when QEMU exits and will have no effect on the underlying image.
    #[serde(default = "const_bool::<false>")]
    pub snapshot: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum VmNet {
    /// User-mode networking (`-netdev user`).
    User(UserNet),
    /// Bridged networking.  This creates a new virtual TAP interface and attaches it to an
    /// existing bridge interface on the host.
    Bridge(BridgeNet),
    /// Unix socket-based networking.  This creates an interface that exchanges network traffic
    /// with another QEMU instance through a Unix socket on the host.
    Unix(UnixNet),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UserNet {
    #[serde(default)]
    pub port_forward: HashMap<String, PortForward>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PortForward {
    /// IP address of the interface to bind to on the host machine.
    ///
    /// This defaults to 127.0.0.1.  This can be set to 0.0.0.0 if other machines on the host's
    /// network should be able to access the forwarded port.
    #[serde(default = "const_string_127_0_0_1")]
    pub outer_host: String,
    pub outer_port: u16,
    /// IP address to forward to within the VM network.
    ///
    /// This defaults to 10.0.2.15, which is the first address assigned by the built-in DHCP
    /// server.  (Specifically, if this is unset in the config, we pass an empty string on the QEMU
    /// command line, which causes QEMU to use the default DHCP address.)
    #[serde(default)]
    pub inner_host: String,
    pub inner_port: u16,
    #[serde(default = "const_port_forward_protocol_tcp")]
    pub proto: PortForwardProtocol,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PortForwardProtocol {
    Tcp,
    Udp,
}

fn const_string_127_0_0_1() -> String {
    "127.0.0.1".into()
}

fn const_port_forward_protocol_tcp() -> PortForwardProtocol {
    PortForwardProtocol::Tcp
}

fn const_string_br0() -> String {
    "br0".into()
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BridgeNet {
    #[serde(default = "const_string_br0")]
    pub bridge: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
enum OneOrMany<T> {
    One(T),
    Many(Vec<T>),
}

impl<T> From<OneOrMany<T>> for Vec<T> {
    fn from(x: OneOrMany<T>) -> Vec<T> {
        match x {
            OneOrMany::One(x) => vec![x],
            OneOrMany::Many(v) => v,
        }
    }
}

fn deserialize_one_or_many<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
where D: Deserializer<'de>, T: Deserialize<'de> {
    let x = OneOrMany::<T>::deserialize(deserializer)?;
    Ok(x.into())
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UnixNet {
    /// Listen on one or more Unix socket paths.  Other QEMU instances can connect to these sockets
    /// to join a virtual network.
    ///
    /// Only a single client can connect to each listening socket.  (This is a limitation of QEMU.)
    /// If multiple clients need to connect to a single server, have the server listen on multiple
    /// sockets and have each client connect to a different listening socket.
    ///
    /// For VMs with multiple listening and/or connecting sockets, traffic is forwarded between all
    /// connections using a QEMU-internal virtual network hub.  To avoid forwarding loops, make
    /// sure the VMs are connected in a tree structure, with no cycles and only a single connection
    /// between each pair of nodes.
    #[serde(default, deserialize_with = "deserialize_one_or_many")]
    pub listen: Vec<PathBuf>,
    /// Connect to one or more Unix socket paths.
    #[serde(default, deserialize_with = "deserialize_one_or_many")]
    pub connect: Vec<PathBuf>,
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
    /// Write output to a file, and provide no input.
    File(FileSerial),
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
#[serde(deny_unknown_fields)]
pub struct FileSerial {
    pub path: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum VmGpio {
    External(ExternalGpio),
    Passthrough(PassthroughGpio),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PassthroughGpio {
    pub device: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalGpio {
    /// Listen on this Unix socket for external GPIO clients.
    pub path: PathBuf,
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
        let Paths {
            ref mut qemu_system_aarch64,
            qemu_system_aarch64_version: _,
            ref mut vhost_device_gpio,
        } = *self;
        if let Some(ref mut path) = qemu_system_aarch64 {
            resolve_relative_path_if_contains_slash(path, base);
        }
        if let Some(ref mut path) = vhost_device_gpio {
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
        let VmDisk { format: _, ref mut path, read_only: _, snapshot: _ } = *self;
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
            VmSerial::File(ref mut fs) => fs.resolve_relative_paths(base),
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

impl FileSerial {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let FileSerial { ref mut path } = *self;
        resolve_relative_path(path, base);
    }
}

impl VmGpio {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        match *self {
            VmGpio::External(ref mut eg) => eg.resolve_relative_paths(base),
            VmGpio::Passthrough(ref mut pg) => pg.resolve_relative_paths(base),
        }
    }
}

impl ExternalGpio {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let ExternalGpio { ref mut path } = *self;
        resolve_relative_path(path, base);
    }
}

impl PassthroughGpio {
    pub fn resolve_relative_paths(&mut self, base: &Path) {
        let PassthroughGpio { ref mut device } = *self;
        resolve_relative_path(device, base);
    }
}
