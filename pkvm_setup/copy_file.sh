#!/bin/bash
set -euo pipefail

disk=$1
f=$2
dest=${3-$(basename "$f")}
shift 2

size=$(stat -L -c %s "$f")

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file="vm_scripts/copy_file_helper.sh" \
  -drive if=virtio,format=raw,file="$f" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append "earlycon root=/dev/vda2 systemd.run=\"/bin/bash /dev/vdb '$dest' $size\""
