#!/bin/bash
set -euo pipefail
# Setup script to be run inside the host VM with `run_vm_script.sh`.

echo "setup_host1.sh ($0) running"

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
hostname=pkvm-host1
edo systemctl start systemd-hostnamed.service
edo hostnamectl hostname "$hostname"
edo sed -i -e "s/pkvm-host/$hostname/g" /etc/hosts

# Generate new SSH host keys
edo rm -f /etc/ssh/ssh_host_*_key /etc/ssh/ssh_host_*_key.pub
edo ssh-keygen -A


# Set network configuration
edo apt install bridge-utils

edo tee /etc/network/interfaces <<"EOF"
source /etc/network/interfaces.d/*

# The loopback network interface
auto lo
iface lo inet loopback

# When run as part of the OpenSUT, this VM has two network adapters (one for
# `-netdev user` and one for `-netdev socket`), which show up as enp0s4 and
# enp0s5.
auto enp0s4
iface enp0s4 inet manual
  # MAC addresses 00:50:56:00:00:00 - 00:50:56:3f:ff:ff are allocated by VMware
  # for use as custom addresses for VMs.
  hwaddress ether 00:50:56:01:01:04
auto enp0s5
iface enp0s5 inet manual
  hwaddress ether 00:50:56:01:01:05

auto br0
iface br0 inet static
  bridge_ports enp0s4 enp0s5
  hwaddress ether 00:50:56:01:01:ff
  # QEMU `-netdev user` assigns addresses 10.0.2.15 - 10.0.2.31 to guests, and
  # uses 10.0.2.2 - 10.0.2.4 for the default gateway and internal services.  We
  # therefore use 10.0.2.100-199 for statically-assigned VMs.
  address 10.0.2.111/24
  gateway 10.0.2.2
EOF

edo tee /etc/resolv.conf <<"EOF"
nameserver 10.0.2.3
EOF

# Allow qemu-bridge-helper to manipulate br0
edo tee /etc/qemu/bridge.conf <<"EOF"
allow br0
EOF


edo apt clean
edo fstrim -v /
