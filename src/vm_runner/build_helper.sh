#!/bin/bash
set -euo pipefail

# Script for building the `vm_runner` project inside a VM.

if [[ "$(id -u)" -eq "0" ]]; then
    # Drop privileges for the rest of the script.
    cp "$0" /tmp/vm-script
    chown user:user /tmp/vm-script
    exec sudo -u user /bin/bash /tmp/vm-script "$@"
fi

cd ~

sudo apt install -y rustc cargo

mkdir -p vm_runner
sudo mount -t 9p -o trans=virtio,version=9p2000.L,rw vm_runner vm_runner

cd vm_runner
ls -l

# Passing `--target` to cargo causes it to use a target-specific build
# directory.  This prevents confusion between artifacts built outside and
# inside the VM when the two are sharing the same directory.
rust_target="$(rustc -vV | sed -n 's/host: //p')"
cargo build --release --target "$rust_target"

echo "Build succeeded"
