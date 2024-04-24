#!/bin/bash
set -euo pipefail

disk=$1
script=$2
shift 2

# Run the Bash script `$script` in the VM, using `$disk` as the disk image.
# This will boot the VM, run the script, and shut down the VM once the script
# terminates.  The boot process has significant overhead (~20 seconds), so
# excessive use of this script will be slow.

mkdir -p outerfs

exec qemu-system-aarch64 -M virt \
  -machine virtualization=true -machine virt,gic-version=3 \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file="$script" \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0,hostfwd=tcp:127.0.0.1:8022-:22 \
  -fsdev local,id=outerfs,path=outerfs,security_model=mapped-xattr \
  -device virtio-9p-pci,fsdev=outerfs,mount_tag=outerfs \
  -nographic \
  -kernel debian-boot/vmlinuz \
  -initrd debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 systemd.run="/bin/bash /dev/vdb"'
