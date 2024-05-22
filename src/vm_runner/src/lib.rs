use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use std::fs;
use std::io;
use std::mem;
use std::os::unix::process::CommandExt;
use std::process::{self, Command, Child};
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


fn build_command(process: &config::Process) -> Command {
    let shell_process = match *process {
        config::Process::Shell(ref x) => x,
        _ => panic!("unimplemented: non-shell processes"),
    };

    let mut cmd = Command::new("/bin/sh");
    cmd.args(&["-c", &shell_process.command]);
    cmd
}


pub fn run_manage(cfg: &Config) -> io::Result<()> {
    let mut children = ManagedProcesses::new();

    for process in &cfg.processes {
        let mut cmd = build_command(process);
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
    assert!(cfg.processes.len() == 1,
        "config error: `mode = 'exec'` requires exactly one entry in `processes`");
    let process = &cfg.processes[0];

    let mut cmd = build_command(process);
    trace!("exec: {:?}", cmd);
    let err = cmd.exec();
    trace!("exec error: {}", err);
    Err(err)
}


pub fn main() {
    let args = env::args_os().collect::<Vec<_>>();
    if args.len() != 2 {
        let cmd_name = env::args().nth(0).unwrap_or_else(|| "vm_runner".to_string());
        eprintln!("usage: {} config.toml", cmd_name);
        process::exit(1);
    }

    let config_str = fs::read_to_string(&args[1]).unwrap();
    let cfg: Config = toml::from_str(&config_str).unwrap();

    match cfg.mode {
        Mode::Manage => run_manage(&cfg).unwrap(),
        Mode::Exec => run_exec(&cfg).unwrap(),
    }
}
