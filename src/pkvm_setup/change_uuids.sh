#!/bin/bash
set -euo pipefail

base_disk=$1
new_disk=$2
shift 2

# Run `vm_scripts/change_uuids_helper.sh` in the VM, with both `$base_disk` and
# `$new_disk` available.  The first disk is mounted and provides the various
# tools needed to modify UUIDs.  The second disk is kept unmounted, since a
# disk's UUID can't be changed while it's mounted.

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$base_disk",read-only=on \
  -drive if=virtio,format=qcow2,file="$new_disk" \
  -drive if=virtio,format=raw,file="$(dirname "$0")/vm_scripts/change_uuids_helper.sh" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 ro init=/bin/bash -- /dev/vdc'
