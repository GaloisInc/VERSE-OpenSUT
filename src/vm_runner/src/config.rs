use std::collections::HashMap;
use indexmap::IndexMap;
use serde::{Serialize, Deserialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub mode: Mode,
    #[serde(default)]
    pub process: Vec<Process>,
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
}

/// Spawn a VM.
///
/// This could instead be done using a `ShellProcess` that invokes QEMU, but using `type = "vm"`
/// handles the most common device options automatically.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VmProcess {
    pub kernel: String,
    pub initrd: Option<String>,
    #[serde(default)]
    pub append: String,

    #[serde(default = "const_u32::<1024>")]
    pub ram_mb: u32,

    /// If set, use KVM.  Otherwise, run emulation with no hardware support.
    ///
    /// Using KVM requires access to the `/dev/kvm` device.
    #[serde(default = "const_true")]
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
    /// GPIO device definitions.  Devices are added in order; the first one listed in the config
    /// file will be `/dev/gpiochip1`, the second will be `/dev/gpiochip2`, and so on.  (Note that
    /// the guest will also have a `gpiochip0` provided automatically by QEMU.)
    #[serde(default)]
    pub gpio: IndexMap<String, VmGpio>,
}

fn const_true() -> bool {
    true
}

fn const_u32<const N: u32>() -> u32 {
    N
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VmDisk {
    pub format: String,
    pub path: String,
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
    pub path: String,
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
    pub device: String,
}
