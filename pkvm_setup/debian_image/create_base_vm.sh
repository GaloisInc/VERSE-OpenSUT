#!/bin/bash
set -euo pipefail

disk=$1
shift 1

SCRIPT_DIR="$(dirname "$0")"


now=$(date +%s)

# These default paths come from the debian-installer-12-netboot-arm64 package:
: ${di_kernel:=/usr/lib/debian-installer/images/12/arm64/text/debian-installer/arm64/linux}
: ${di_initrd:=/usr/lib/debian-installer/images/12/arm64/text/debian-installer/arm64/initrd.gz}

if ! [[ -f "$di_kernel" ]]; then
    echo "Error: debian-installer kernel not found at $di_kernel" 1>&2
    echo "Install debian-installer-12-netboot-arm64 or set di_kernel=<path>" 1>&2
    exit 1
fi
if ! [[ -f "$di_initrd" ]]; then
    echo "Error: debian-installer initrd not found at $di_initrd" 1>&2
    echo "Install debian-installer-12-netboot-arm64 or set di_initrd=<path>" 1>&2
    exit 1
fi

# Add `preseed.cfg` and `preseed_late_command.sh` to the initrd.  These are
# used to automate the Debian installation process.  The initrd can actually
# consist of several different .cpio.gz files concatenated together, so we can
# just append a new chunk instead of modifying the existing one.
preseeded_initrd=initrd.preseed-$now.gz
cp -v "$di_initrd" "$preseeded_initrd"
(
    cd $SCRIPT_DIR
    ls ./preseed.cfg ./preseed_late_command.sh | cpio -H newc -o
) | gzip >>"$preseeded_initrd"


# Create a new, empty disk image at the location indicated by the user.
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

debian_boot_tar=debian_boot-$now.tar
qemu-img create -f raw "$debian_boot_tar" 128M

# Run the VM.  This will install Debian into the new disk image.
qemu-system-aarch64 -M virt \
  -cpu cortex-a72 -smp 4 -m 4096 \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file="$debian_boot_tar" \
  -device virtio-scsi-pci,id=scsi0 \
  -object rng-random,filename=/dev/urandom,id=rng0 \
  -device virtio-rng-pci,rng=rng0 \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0 \
  -nographic \
  -kernel "$di_kernel" \
  -initrd "$preseeded_initrd"

# debian-installer doesn't reset the terminal mode before exiting.
reset

# Extract the boot files from `debian_boot.tar`.
out_dir="$(dirname "$disk")"
mkdir -p "$out_dir/debian-boot"
echo "extracting $debian_boot_tar into $out_dir/debian-boot:"
tar -C "$out_dir/debian-boot" -xvf "$debian_boot_tar"

if [[ -z "${keep_temp_files-}" ]]; then
    rm -v "$preseeded_initrd" || true
    rm -v "$debian_boot_tar" || true
fi
