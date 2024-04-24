#!/bin/bash
set -euo pipefail

echo "change_disk_uuids.sh ($0) running"

echo
echo "initial block devices:"
blkid /dev/vd*
echo

# Assign new UUIDs to the three partitions of /dev/vdb.  `clone_base_vm.sh`
# runs this inside the new VM, in place of `init`.  Note that since we're
# running in place of `init`, the system is not properly booted - some
# filesystems aren't mounted, no services are available, and so on.
#
# This only changes the filesystem UUID (what `blkid` calls `UUID`), not the
# partition UUID stored in the MBR (`PARTUUID`).  We should ideally change
# both, but `PARTUUID` is both more work to change (`gdisk` is not easily
# scriptable) and less commonly used.  This also does not change the UUID for
# the whole disk (`/dev/vdb`) stored in the GPT partition table.

edo() {
    echo " >> $*" 1>&2
    "$@"
}


# Helper function for setting the UUID of a disk.  Takes the new UUID as an
# argument, and prints the old UUID to stdout.
set_uuid() {
    local disk="$1"
    local new_uuid="$2"
    shift 1
    local old_uuid="$(blkid "$disk" --match-tag UUID --output value)"
    local type="$(blkid "$disk" --match-tag TYPE --output value)"
    echo "setting UUID of $type partition $disk to $new_uuid" 1>&2
    case "$type" in
        ext[234])
            # tune2fs unfortunately requires the disk to be fsck'd, even when
            # it's only changing the UUID.  And fsck won't work on a disk
            # that's mounted read-write.
            edo e2fsck -fp "$disk" 1>&2
            edo tune2fs -U "$new_uuid" "$disk" 1>&2
            ;;
        swap)
            edo swaplabel -U "$new_uuid" "$disk" 1>&2
            ;;
        *)
            echo "unknown disk type $type for $disk" 1>&2
            return 1
            ;;
    esac
    echo "$old_uuid"
}

random_uuid() {
    cat /proc/sys/kernel/random/uuid
}

# Root FS needs special handling, since it must be unmounted for `set_uuid` to
# work on it.
new_root_uuid="$(random_uuid)"
old_root_uuid="$(edo set_uuid /dev/vdb2 $new_root_uuid)"

edo mount /dev/vdb2 /mnt
edo sed -i -e "s/$old_root_uuid/$new_root_uuid/g" /mnt/etc/fstab

# Now the root fs is mounted

# Higher-level helper for changing UUIDs.  This changes the UUID to a new one
# chosen at random, and updates /etc/fstab accordingly.
update_uuid() {
    local disk="$1"
    local new_uuid="$(random_uuid)"
    local old_uuid="$(edo set_uuid "$disk" $new_uuid)"
    edo sed -i -e "s/$old_uuid/$new_uuid/g" /mnt/etc/fstab
}

edo update_uuid /dev/vdb1
edo update_uuid /dev/vdb3


echo
echo "final block devices:"
blkid /dev/vd*
echo


# Since this script runs in place of init, we're responsible for shutting down
# the system (somewhat) cleanly.
mount -o remount,ro /
poweroff -f
