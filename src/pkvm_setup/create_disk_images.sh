#!/bin/bash
set -euo pipefail

mkdir -p vms

disk_base=vms/disk_base.img
disk_common=vms/disk_common.img
disk_host=vms/disk_host.img
disk_guest=vms/disk_guest.img
disk_host_dev=vms/disk_host_dev.img
disk_guest_dev=vms/disk_guest_dev.img


edo() {
    echo " >> $*"
    "$@"
}

get_img_info() {
    qemu-img info --output=json "$1" | jq -r -e ".\"$2\""
}

compress_image() {
    local src="$1"
    local dest="$2"
    shift 2

    local qemu_args=( -c -O qcow2 )
    if backing="$(get_img_info "$src" backing-filename)"; then
        if backing_format="$(get_img_info "$src" backing-filename-format)"; then
            qemu_args+=( -B "$backing" -F "$backing_format" )
        else
            echo "error: image $src has backing-filename but no backing-filename-format" 1>&2
            exit 1
        fi
    fi
    edo qemu-img convert "${qemu_args[@]}" "$src" "$dest"
}

derive_image() {
    local src="$1"
    local dest="$2"
    shift 2

    local src_rel="$(realpath --relative-to "$(dirname "$dest")" "$src")"
    local backing_format="$(get_img_info "$src" format)"
    edo qemu-img create -f qcow2 -b "$src_rel" -F "$backing_format" "$dest"
}


compress_helper() {
    local img="$1"
    local desc="$2"
    shift 2

    edo compress_image "$img.orig" "$img"
    ls -l "$img.orig"
    ls -l "$img"
    echo "created $desc image $img"
    edo rm -v "$img.orig"
}


# `disk_base` consists of a Debian installation and nothing else.  This is
# managed separate from `disk_common` so `disk_common` can be rebuilt without
# rerunning the entire install, which takes about 1.5 hours.
if [[ -e "$disk_base" ]]; then
    echo "keeping existing $disk_base" 1>&2
else
    if ! [[ -e "$disk_base.orig" ]]; then
        bash debian_image/create_base_vm.sh "$disk_base.orig"
    fi
    compress_helper "$disk_base" base
fi

# `disk_common` is a copy of `disk_base` with additional software and
# configuration that's common to both the host and the guest.  It's also
# cleaned and trimmed to reduce its compressed size.
if [[ -e "$disk_common" ]]; then
    echo "keeping existing $disk_common" 1>&2
else
    if ! [[ -e "$disk_common.orig" ]]; then
        # Copy instead of using `derive_image` so `fstrim` can trim the combine
        # base+common image.  `fstrim` can only trim the final read-write image
        # in a backing chain.
        edo cp -v "$disk_base" "$disk_common.orig"
        edo bash run_vm_script.sh "$disk_common.orig" vm_scripts/setup_common.sh
    fi
    compress_helper "$disk_common" common
    # Mark `disk_common` read-only.  It's used as a backing file for
    # `disk_host` and `disk_guest`, so modifying it would cause data
    # corruption.
    edo chmod -v a-w "$disk_common"
fi

# `disk_host` and `disk_guest` is a delta on top of `disk_common` with host-
# or guest-specific software.

if [[ -e "$disk_host" ]]; then
    echo "keeping existing $disk_host" 1>&2
else
    if ! [[ -e "$disk_host.orig" ]]; then
        edo derive_image "$disk_common" "$disk_host.orig"
        edo bash change_uuids.sh "$disk_common" "$disk_host.orig"
        edo bash run_vm_script.sh "$disk_host.orig" vm_scripts/setup_host.sh
    fi
    compress_helper "$disk_host" host
fi

if [[ -e "$disk_guest" ]]; then
    echo "keeping existing $disk_guest" 1>&2
else
    if ! [[ -e "$disk_guest.orig" ]]; then
        edo derive_image "$disk_common" "$disk_guest.orig"
        edo bash change_uuids.sh "$disk_common" "$disk_guest.orig"
        edo bash run_vm_script.sh "$disk_guest.orig" vm_scripts/setup_guest.sh
    fi
    compress_helper "$disk_guest" guest
fi

# `disk_host_dev` and `disk_guest_dev` are copies of `disk_host` and
# `disk_guest`.  They aren't deltas backed by `disk_host`/`disk_guest` because
# those images might change (e.g. adding new log entries each time the VM is
# booted).

if [[ -e "$disk_host_dev" ]]; then
    echo "keeping existing $disk_host_dev" 1>&2
else
    edo cp -v "$disk_host" "$disk_host_dev"
fi

if [[ -e "$disk_guest_dev" ]]; then
    echo "keeping existing $disk_guest_dev" 1>&2
else
    edo cp -v "$disk_guest" "$disk_guest_dev"
fi
