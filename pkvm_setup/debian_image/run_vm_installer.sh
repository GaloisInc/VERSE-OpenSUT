#!/bin/bash
set -euo pipefail

initrd=$1
disk=$2
shift 1

exec qemu-system-aarch64 -M virt \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -drive if=virtio,format=qcow2,file="$disk" \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0 \
  -nographic \
  -kernel /usr/lib/debian-installer/images/12/arm64/text/debian-installer/arm64/linux \
  -initrd "$initrd"
