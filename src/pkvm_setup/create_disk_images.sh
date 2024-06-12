#!/bin/bash
set -euo pipefail

mkdir -p vms

disk_base=vms/disk_base.img
disk_common=vms/disk_common.img
disk_host=vms/disk_host.img
disk_guest=vms/disk_guest.img
disk_host_dev=vms/disk_host_dev.img
disk_guest_dev=vms/disk_guest_dev.img


pkvm_version=6.4.0
pkvm_rev=beb7002f98c0


edo() {
    echo " >> $*" 1>&2
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

find_linux_image_deb() {
    local version="$1"
    local tag="$2"
    local rev="$3"
    shift 3

    local x="$version-$tag-g$rev"
    local y="$version-g$rev"

    local candidates=( linux-image-${x}_${y}-[0-9]*_arm64.deb )
    if [[ "${#candidates[@]}" -eq 1 ]]; then
        if [[ -f "${candidates[0]}" ]]; then
            echo "${candidates[0]}"
        else
            # If no matching files exist, `$candidates` will be a 1-element
            # array containing the unexpanded glob pattern.
            echo "Error: found no candidate .deb matching ${candidate[0]}" 1>&2
            return 1
        fi
    else
        echo "Error: found multiple candidate files:" 1>&2
        for f in "${candidates[@]}"; do
            echo "  $f" 1>&2
        done
        echo "Remove all but one and try again" 1>&2
        return 1
    fi
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

        # Prepare storage for the kernel packages and the extracted kernel and
        # initrd images.
        tar_file=$(mktemp $(pwd)/kernel.XXXXXX.tar)
        edo dd if=/dev/zero of="$tar_file" bs=1M count=256
        pkvm_kernel_deb="$(find_linux_image_deb ${pkvm_version} pkvm ${pkvm_rev})"
        # Could add more packages if needed, e.g. linux-headers
        edo tar -c "$pkvm_kernel_deb" | edo dd of="$tar_file" conv=notrunc

        edo bash run_vm_script.sh "$disk_common.orig" vm_scripts/setup_common.sh "$tar_file"

        edo mkdir -p vms/pkvm-boot
        edo tar -C vms/pkvm-boot -xf "$tar_file"
        edo rm -f "$tar_file"
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
