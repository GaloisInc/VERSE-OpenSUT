#!/bin/bash
set -euo pipefail

mkdir -p vms

disk_base=vms/disk_base.img
disk_host=vms/disk_host.img
disk_host_dev=vms/disk_host_dev.img
disk_guest=vms/disk_guest.img
disk_guest_dev=vms/disk_guest_dev.img

if [[ -e "$disk_base" ]]; then
    echo "keeping existing $disk_base" 1>&2
else
    bash debian_image/create_base_vm.sh "$disk_base"
    echo "created base image $disk_base"
fi

if [[ -e "$disk_host" ]]; then
    echo "keeping existing $disk_host" 1>&2
else
    bash debian_image/clone_vm.sh "$disk_base" "$disk_host"
    bash run_vm_script.sh "$disk_host" debian_image/setup_host_vm.sh
    echo "created host image $disk_host"
fi

if [[ -e "$disk_host_dev" ]]; then
    echo "keeping existing $disk_host_dev" 1>&2
else
    bash debian_image/clone_vm.sh "$disk_base" "$disk_host_dev"
    bash run_vm_script.sh "$disk_host_dev" debian_image/setup_host_vm.sh
    bash run_vm_script.sh "$disk_host_dev" debian_image/setup_host_vm_interactive.sh
    echo "created host dev image $disk_host_dev"
fi

if [[ -e "$disk_guest" ]]; then
    echo "keeping existing $disk_guest" 1>&2
else
    bash debian_image/clone_vm.sh "$disk_base" "$disk_guest"
    bash run_vm_script.sh "$disk_guest" debian_image/setup_guest_vm.sh
    echo "created guest image $disk_guest"
fi

if [[ -e "$disk_guest_dev" ]]; then
    echo "keeping existing $disk_guest_dev" 1>&2
else
    bash debian_image/clone_vm.sh "$disk_base" "$disk_guest_dev"
    bash run_vm_script.sh "$disk_guest_dev" debian_image/setup_guest_vm.sh
    echo "created guest dev image $disk_guest_dev"
fi
