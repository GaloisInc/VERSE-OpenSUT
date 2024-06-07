#!/bin/bash
set -euo pipefail

# Script for installing `vm_runner` binaries into the current VM image.

if [[ "$(id -u)" -eq "0" ]]; then
    # Drop privileges for the rest of the script.
    cp "$0" /tmp/vm-script
    chown user:user /tmp/vm-script
    exec sudo -u user /bin/bash /tmp/vm-script "$@"
fi

cd ~

mkdir -p vm_runner
sudo mount -t 9p -o trans=virtio,version=9p2000.L,rw vm_runner vm_runner

sudo mkdir -p /opt/opensut/bin
target=aarch64-unknown-linux-gnu
sudo cp -v \
    vm_runner/target/"$target"/release/opensut_vm_runner \
    vm_runner/target/"$target"/release/opensut_boot \
    /opt/opensut/bin
