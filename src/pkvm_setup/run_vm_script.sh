#!/bin/bash
set -euo pipefail

# Usage: run_vm_script.sh DISK.img SCRIPT.sh [INPUT]
#
# Run the Bash script `SCRIPT.sh` in the VM, using `DISK.img` as the disk
# image.  This will boot the VM, run the script, and shut down the VM once the
# script terminates.  The boot process has significant overhead (~20 seconds),
# so excessive use of this script will be slow.
#
# If an `INPUT` file is provided, it will be passed into the VM and its path
# within the VM will be passed to `SCRIPT.sh` as a command-line argument.  Note
# that the method this script uses to pass `INPUT` into the VM may cause it to
# be padded with extra zero bytes.  Some tools, such as `tar` will ignore these
# trailing zeros, but other tools may have difficulty.

case "$#" in
    2|3) ;;
    *)
        echo "usage: $0 DISK.img SCRIPT.sh [INPUT]" 1>&2
        exit 1
        ;;
esac

disk=$1
script=$2

args=(
    -drive if=virtio,format=qcow2,file="$disk",discard=unmap
    -drive if=virtio,format=raw,file="$script"
    -kernel vms/debian-boot/vmlinuz
    -initrd vms/debian-boot/initrd.img
)
kernel_args='earlycon root=/dev/vda2 systemd.run="/bin/bash /dev/vdb"'

if [[ "$#" -eq 3 ]]; then
    args+=( -drive if=virtio,format=raw,file="$3" )
    kernel_args='earlycon root=/dev/vda2 systemd.run="/bin/bash /dev/vdb /dev/vdc"'
fi

exec bash "$(dirname "$0")/run_vm_common.sh" \
    "${args[@]}" \
    -append "$kernel_args"
