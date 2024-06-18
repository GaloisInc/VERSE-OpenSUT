#!/bin/bash
set -euo pipefail
# Setup script to be run inside the host VM with `run_vm_script.sh`.

echo "setup_host.sh ($0) running"

edo() {
    echo " >> $*"
    "$@"
}


# Assign a new machine ID
edo rm -f /etc/machine-id /var/lib/dbus/machine-id
edo dbus-uuidgen --ensure=/etc/machine-id
# With no argument, `--ensure` updates `/var/lib/dbus/machine-id`
edo dbus-uuidgen --ensure

# Change the hostname
hostname=pkvm-host
edo systemctl start systemd-hostnamed.service
edo hostnamectl hostname "$hostname"
edo sed -i -e "s/verse-opensut-vm/$hostname/g" /etc/hosts

# Generate new SSH host keys
edo rm -f /etc/ssh/ssh_host_*_key /etc/ssh/ssh_host_*_key.pub
edo ssh-keygen -A


# Extract the new packages from input $1 and install them.
work_dir="$(mktemp -d)"
edo tar -C "$work_dir" -xf "$1"
# Using `apt install foo.deb` instead of `dpkg -i foo.deb` will install any
# missing dependencies in addition to `foo.deb` itself.  Providing all debs at
# once means we don't have to figure out the correct dependency order between
# them.
edo apt install -y --no-install-recommends "$work_dir"/*.deb
edo rm -rf "$work_dir"

# Additional packages
edo apt install -y --no-install-recommends ipxe-qemu

# Allow `user` to access /dev/kvm and start VMs
edo usermod -a -G kvm user


edo apt clean
edo fstrim -v /
