#!/bin/bash
set -euo pipefail

disk=$1
shift 1

# Run a root shell (`init=/bin/bash`) in the VM, using `$disk` as the disk
# image.  Useful for recovering if you've accidentally made the OS on `$disk`
# unbootable.  Note that the filesystem will initially be mounted read-only;
# run `mount -o remount,rw /` to change that.

mkdir -p outerfs

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 init=/bin/bash ro'
