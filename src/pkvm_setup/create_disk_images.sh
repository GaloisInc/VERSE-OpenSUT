#!/bin/bash
set -euo pipefail

mkdir -p vms

disk_base=vms/disk_base.img
disk_host=vms/disk_host.img
disk_guest=vms/disk_guest.img

# Building these disk images is rather expensive, so don't overwrite existing
# ones.
for disk in "$disk_base" "$disk_host" "$disk_guest"; do
    if [[ -e "$disk" ]]; then
        echo "error: refusing to overwrite existing $disk" 1>&2
        #exit 1
    fi
done

bash debian_image/create_base_vm.sh "$disk_base"

bash debian_image/clone_vm.sh "$disk_base" "$disk_host"
bash run_vm_script.sh "$disk_host" debian_image/setup_host_vm.sh
# This part is optional, but convenient for interactive use:
bash run_vm_script.sh "$disk_host" debian_image/setup_host_vm_interactive.sh

bash debian_image/clone_vm.sh "$disk_base" "$disk_guest"
bash run_vm_script.sh "$disk_guest" debian_image/setup_guest_vm.sh

echo
echo "created host image $disk_host"
echo "created guest image $disk_guest"
