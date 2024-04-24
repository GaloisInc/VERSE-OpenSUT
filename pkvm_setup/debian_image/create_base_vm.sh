#!/bin/bash
set -euo pipefail

disk=$1
shift 1


# Prepare a Debian netinst initrd with preseed.cfg injected into it.

kernel=/usr/lib/debian-installer/images/12/arm64/text/debian-installer/arm64/linux
initrd=/usr/lib/debian-installer/images/12/arm64/text/debian-installer/arm64/initrd.gz
cp -v "$initrd" initrd.preseed.gz

# Add `preseed.cfg` and `preseed_late_command.sh` to the initrd.  The initrd
# can actually consist of several different .cpio.gz files concatenated
# together, so we can just append a new chunk instead of modifying the existing
# one.
ls ./preseed.cfg ./preseed_late_command.sh | cpio -H newc -o | gzip >>initrd.preseed.gz


qemu-img create -f qcow2 "$disk" 16G

# In addition to populating the disk image `$disk` with a Debian installation,
# we also need to extract the boot files (kernel and initrd) from the new
# installation so we can pass them to later QEMU invocations.  Here is our
# strategy for this:
#
# 1. In addition to providing `$disk` as `/dev/vda`, also provide a small raw
#    image as `/dev/vdb`.  The name of this image is `debian_boot.tar`.
# 2. At the end of installation, `tar` up the boot files from `/target/boot`
#    and write the archive directly to the block device `/dev/vdb`.  (This is
#    done by the `late_command` at the bottom of `preseed.cfg`.)
# 3. After the installation VM terminates, since `debian_boot.tar` is a raw
#    image, it contains exactly the archive produced in step 2 (padded with
#    zeros, which is fine) and can be extracted with `tar` on the host.
#
# We previously tried using the 9p filesystem over virtio (QEMU's `-fsdev`
# option), but this requires kernel modules that aren't included in the Debian
# installer.  Currently, debian-installer installs into `/target` both the
# latest kernel and also the kernel version used by debian-installer itself,
# complete with the full set of modules, so it's possible to load the modules
# with `in-target modprobe -a 9p 9pnet_virtio`.  However, this seems
# potentially fragile, so we now use the `tar`-based approach, which doesn't
# require any special modules.

qemu-img create -f raw debian_boot.tar 128M

qemu-system-aarch64 -M virt \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file=debian_boot.tar \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0 \
  -nographic \
  -kernel "$kernel" \
  -initrd initrd.preseed.gz

mkdir -p debian-boot
tar -C debian-boot -xvf debian_boot.tar
