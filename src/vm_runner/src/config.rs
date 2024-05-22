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
    // TODO
}
