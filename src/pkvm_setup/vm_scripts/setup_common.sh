#!/bin/bash
set -euo pipefail
# Setup script to be run inside the common VM image with `run_vm_script.sh`.

echo "setup_common.sh ($0) running"

edo() {
    echo " >> $*"
    "$@"
}

# Enable passwordless sudo for `user`
edo tee -a /etc/sudoers <<EOF
user ALL=(ALL) NOPASSWD: ALL
EOF


# Install custom packages.

# Collect old kernel packages so they can be removed later.  One of the custom
# packages will be a new kernel, which we install first before removing the old
# ones.  This causes the `/boot/vmlinuz` and `/boot/initrd.img` symlinks to be
# updated to point to the new kernel, whereas removing the old kernels first
# causes the symlinks to be deleted entirely.
old_kernel_pkgs="$(dpkg -l | grep linux-image | while read status pkg rest; do echo "$pkg"; done)"

# Extract the new packages from input $1 and install them.
work_dir="$(mktemp -d)"
edo tar -C "$work_dir" -xf "$1"
(
    cd "$work_dir"
    for f in *.deb; do
        edo dpkg -i "$f"
    done
)
edo rm -rf "$work_dir"

# Remove the old kernel packages.  The `noninteractive` frontend suppresses a
# confirmation dialog about uninstalling the running kernel.
DEBIAN_FRONTEND=noninteractive apt purge -y $old_kernel_pkgs

# Export the new kernel and initrd images back through $1.
edo tar -chf "$1" -C /boot vmlinuz initrd.img


edo apt clean
edo fstrim -v /
