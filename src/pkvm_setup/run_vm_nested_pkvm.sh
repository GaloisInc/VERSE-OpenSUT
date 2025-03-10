#!/bin/bash
set -euo pipefail

disk_host=$1
disk_guest=$2
shift 2

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk_host" \
  -drive if=virtio,format=qcow2,file="$disk_guest" \
  -kernel vms/pkvm-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 nokaslr kvm-arm.mode=protected'
