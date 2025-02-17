#!/bin/bash
set -euo pipefail
# Setup script to be run inside the host VM with `run_vm_script.sh`.

echo "setup_guest_logging.sh ($0) running"

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
hostname=pkvm-guest-logging
edo systemctl start systemd-hostnamed.service
edo hostnamectl hostname "$hostname"
edo sed -i -e "s/pkvm-guest/$hostname/g" /etc/hosts

# Generate new SSH host keys
edo rm -f /etc/ssh/ssh_host_*_key /etc/ssh/ssh_host_*_key.pub
edo ssh-keygen -A


# Set network configuration
edo tee /etc/network/interfaces <<"EOF"
source /etc/network/interfaces.d/*

# The loopback network interface
auto lo
iface lo inet loopback

auto enp0s4
iface enp0s4 inet static
  hwaddress ether 00:50:56:02:04:04
  address 10.0.2.124/24
  gateway 10.0.2.2
EOF

edo tee /etc/resolv.conf <<"EOF"
nameserver 10.0.2.3
EOF


edo apt install -y cryptsetup


edo apt clean
edo fstrim -v /
