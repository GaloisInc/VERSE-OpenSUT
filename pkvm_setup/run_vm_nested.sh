#!/bin/bash
set -euo pipefail

disk_host=$1
disk_guest=$2
shift 2

mkdir -p outerfs

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk_host" \
  -drive if=virtio,format=qcow2,file="$disk_guest" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2'
