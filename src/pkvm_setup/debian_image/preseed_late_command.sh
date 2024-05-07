#!/bin/sh
set -e

# Disable resume and rebuild the initrd.
echo 'RESUME=none' >/target/etc/initramfs-tools/conf.d/resume
in-target update-initramfs -u

# Tar up the boot files and write the tar directly to /dev/vdb.  See
# run_vm_installer.sh for details on why we do this.
tar -chf /dev/vdb -C /target/boot vmlinuz initrd.img
