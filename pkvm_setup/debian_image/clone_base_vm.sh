#!/bin/bash
set -euo pipefail

base_disk=$1
new_disk=$2
shift 2

cp -v "$base_disk" "$new_disk"

# Boot the VM and run a script to assign new UUIDs to the disks in the new VM.
# When running tests, we provide both the host and guest disks to the host VM,
# so it can pass through the guest disk to the guest VM it runs.  The host and
# guest disks are both derived from the same base image, but we need them to
# have distinct UUIDs so various daemons in the host VM don't confuse the two.

exec qemu-system-aarch64 -M virt \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -drive if=virtio,format=qcow2,file="$base_disk" \
  -drive if=virtio,format=qcow2,file="$new_disk" \
  -drive if=virtio,format=raw,file="$(dirname "$0")/change_disk_uuids.sh" \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0,hostfwd=tcp::8022-:22 \
  -nographic \
  -kernel debian-boot/vmlinuz \
  -initrd debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 ro init=/bin/bash -- /dev/vdc'
