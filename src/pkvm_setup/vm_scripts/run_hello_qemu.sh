#!/bin/bash
set -euo pipefail

# Run the Hello World example kernel under KVM.  This is intended to be used
# inside the host VM.

# For the network device, we set `romfile=""` to skip loading the iPXE ROM.
# Otherwise QEMU will complain that it's not found.  We don't currently use PXE
# for anything, so it's fine to disable this.

qemu/build/qemu-system-aarch64 \
    -M virt -cpu host -enable-kvm \
    -smp 2 -m 1024 \
    -device virtio-scsi-pci,id=scsi0 \
    -object rng-random,filename=/dev/urandom,id=rng0 \
    -device virtio-rng-pci,rng=rng0 \
    -device virtio-net-pci,netdev=net0,romfile="" \
    -netdev user,id=net0,hostfwd=tcp:127.0.0.1:8022-:22 \
    -fsdev local,id=outerfs,path=outerfs,security_model=mapped-xattr \
    -device virtio-9p-pci,fsdev=outerfs,mount_tag=outerfs \
    -nographic \
    -kernel hello/kernel.elf
