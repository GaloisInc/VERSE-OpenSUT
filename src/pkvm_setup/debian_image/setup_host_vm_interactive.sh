#!/bin/bash
set -euo pipefail
# Additional setup script for host VMs that will be used interactively.

echo "setup_host_vm_interactive.sh ($0) running"

edo() {
    echo " >> $*"
    "$@"
}


# Install some tools for convenience.
edo apt install -y git vim tmux htop socat


# Automatically mount `outerfs` on boot
edo tee -a /etc/fstab <<EOF
outerfs	/home/user/outerfs	9p	trans=virtio,version=9p2000.L,rw	0	0
EOF
# Create the mountpoint, and make sure `user` owns it.
edo mkdir /home/user/outerfs || true
edo chown user:user /home/user/outerfs
# Mount the 9p filesystem, and make sure `user` owns the root of it.
edo mount /home/user/outerfs
edo chown user:user /home/user/outerfs
