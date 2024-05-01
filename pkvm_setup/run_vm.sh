#!/bin/bash
set -euo pipefail

disk=$1
shift 1

mkdir -p outerfs

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2'
