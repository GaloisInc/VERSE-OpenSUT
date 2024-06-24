#!/bin/bash
set -euo pipefail
# Setup script to be run inside the guest VM with `run_vm_script.sh`.

echo "setup_guest_vm.sh ($0) running"

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
hostname=pkvm-guest
edo systemctl start systemd-hostnamed.service
edo hostnamectl hostname "$hostname"
edo sed -i -e "s/verse-opensut-vm/$hostname/g" /etc/hosts

# Generate new SSH host keys
edo rm -f /etc/ssh/ssh_host_*_key /etc/ssh/ssh_host_*_key.pub
edo ssh-keygen -A


# Allow `user` to access /dev/kvm and start VMs
edo usermod -a -G kvm user

# Enable passwordless sudo for `user`
edo tee -a /etc/sudoers <<EOF
user ALL=(ALL) NOPASSWD: ALL
EOF
