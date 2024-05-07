#!/bin/bash
set -euo pipefail

disk=$1
script=$2
shift 2

# Run the Bash script `$script` in the VM, using `$disk` as the disk image.
# This will boot the VM, run the script, and shut down the VM once the script
# terminates.  The boot process has significant overhead (~20 seconds), so
# excessive use of this script will be slow.

exec bash "$(dirname "$0")/run_vm_common.sh" \
  -drive if=virtio,format=qcow2,file="$disk" \
  -drive if=virtio,format=raw,file="$script" \
  -kernel vms/debian-boot/vmlinuz \
  -initrd vms/debian-boot/initrd.img \
  -append 'earlycon root=/dev/vda2 systemd.run="/bin/bash /dev/vdb"'
