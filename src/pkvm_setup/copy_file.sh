#!/bin/bash
set -euo pipefail

pkvm_dir="$(dirname "$0")"

disk=$1
f=$2
dest=${3-$(basename "$f")}
shift 2

size=$(stat -L -c %s "$f")
mode=$(stat -L -c %a "$f")

exec bash "$pkvm_dir/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file="$pkvm_dir/vm_scripts/copy_file_helper.sh" \
  -drive if=virtio,format=raw,file="$f" \
  -kernel "$pkvm_dir/vms/debian-boot/vmlinuz" \
  -initrd "$pkvm_dir/vms/debian-boot/initrd.img" \
  -append "earlycon root=/dev/vda2 systemd.run=\"/bin/bash /dev/vdb '$dest' $size $mode\""
