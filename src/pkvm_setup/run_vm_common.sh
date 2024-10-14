#!/bin/bash
set -euo pipefail

# Run QEMU with arguments common to all `run_vm*.sh` scripts.  The caller
# should provide additional arguments to set the disks and kernel/initrd.
#
# To enable port forwarding or otherwise adjust the network settings, set
# `$NETDEV_USER_EXTRA_ARGS` to an additional string to append to the `-netdev
# user` argument.  For example, to forward port 8022 to 22 for SSH:
#   NETDEV_USER_EXTRA_ARGS=,hostfwd=tcp:127.0.0.1:8022-:22

mkdir -p outerfs

exec qemu-system-aarch64 -M virt \
  -machine virtualization=true -machine virt,gic-version=3 \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev "user,id=net0${NETDEV_USER_EXTRA_ARGS:-}" \
  -fsdev local,id=outerfs,path=outerfs,security_model=mapped-xattr \
  -device virtio-9p-pci,fsdev=outerfs,mount_tag=outerfs \
  -nographic \
  "$@"
