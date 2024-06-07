use std::env;
use std::process;

use env_logger;
use opensut_vm_runner;

fn main() {
    env_logger::init();

    let args = env::args_os().collect::<Vec<_>>();
    if args.len() != 2 {
        let cmd_name = env::args().nth(0).unwrap_or_else(|| "vm_runner".to_string());
        eprintln!("usage: {} config.toml", cmd_name);
        process::exit(1);
    }

    opensut_vm_runner::runner_main(&args[1]);
}
