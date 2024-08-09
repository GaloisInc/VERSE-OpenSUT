#!/bin/bash
set -euo pipefail

# This script builds the disk images for all of the OpenSUT host and guest VMs.
# These contain some common dependencies and configuration, but no application
# code; applications such as MPS are provided as a separate "applicastion
# partition" when running the VM.  (The difference is that the VM image created
# by this script is considered "trusted", but the application image is not and
# must be integrity-checked before use.)
#
# To keep the total size of the images under control, we use QEMU's transparent
# compression and snapshot/delta features.  We build a tree of images, where
# each disk image in the tree (except the root) is a delta based on its parent
# image.  Each image is also compressed once we're done writing to it (writing
# to a compressed image may overwrite compressed blocks with uncompressed
# ones).
#
# Here is the tree of images we create:
#
# * common
#   * host
#   * host_dev
#   * guest
#   * guest_dev
#
# `host_dev` and `guest_dev` are generic host/guest images for development and
# testing.  The remaining `host*` and `guest*` images are used for running the
# OpenSUT.  The `common*` images contain packages common to multiple host/guest
# images and are used to keep the total size of the images down.

mkdir -p vms

disk() {
    echo "vms/disk_$1.img"
}


pkvm_version=6.4.0
pkvm_rev=beb7002f98c0


edo() {
    echo " >> $*" 1>&2
    "$@"
}

get_img_info() {
    qemu-img info --output=json "$1" | jq -r -e ".\"$2\""
}

derive_image() {
    local src="$1"
    local dest="$2"
    shift 2

    local src_rel
    src_rel="$(realpath --relative-to "$(dirname "$dest")" "$src")"
    local backing_format
    backing_format="$(get_img_info "$src" format)"
    edo qemu-img create -f qcow2 -b "$src_rel" -F "$backing_format" "$dest"
}


compress_helper() {
    local img="$1"
    local desc="$2"
    shift 2

    bash compress_disk_image.sh "$img.orig" "$img"
    ls -l "$img.orig"
    ls -l "$img"
    echo "created $desc image $img"
    edo rm -v "$img.orig"
}

# `sole_file foo_*.deb` gets the name of the sole existing file matching
# `foo_*.deb`.  If there are multiple matching files or none at all, it reports
# an error.
sole_file() {
    if [[ "$#" -eq 1 ]]; then
        if [[ -f "$1" ]]; then
            echo "$1"
        else
            # Typically, this function is called like `sole_file foo_*.deb`, so
            # if no matching files are found, the unexpanded glob pattern is
            # passed as the first argument.
            echo "Error: found no file matching $1" 1>&2
            return 1
        fi
    elif [[ "$#" -eq 0 ]]; then
        echo "Error: called sole_file with no arguments" 1>&2
        return 1
    else
        echo "Error: found multiple candidate files:" 1>&2
        for f in "$@"; do
            echo "  $f" 1>&2
        done
        echo "Remove all but one and try again" 1>&2
        return 1
    fi
}

find_linux_image_deb() {
    local version="$1"
    local tag="$2"
    local rev="$3"
    shift 3

    local x="$version-$tag-g$rev"
    local y="$version-g$rev"

    sole_file linux-image-"${x}"_"${y}"-[0-9]*_arm64.deb
}


define_image() {
    local name="$1"
    local disk
    disk="$(disk "$name")"

    if [[ -e "$disk" ]]; then
        echo "keeping existing $disk" 1>&2
    else
        if ! [[ -e "$disk.orig" ]]; then
            "do_img_$name"
        fi
        compress_helper "$disk" "$name"
    fi
}

define_image_readonly() {
    local name="$1"
    local disk
    disk="$(disk "$name")"

    if [[ -e "$disk" ]]; then
        echo "keeping existing $disk" 1>&2
    else
        if ! [[ -e "$disk.orig" ]]; then
            "do_img_$name"
        fi
        compress_helper "$disk" "$name"
        edo chmod -v a-w "$disk"
    fi
}

define_image_copy() {
    local src="$1"
    local dest="$2"

    if [[ -e "$(disk "$dest")" ]]; then
        echo "keeping existing $(disk "$dest")" 1>&2
    else
        edo cp -v "$(disk "$src")" "$(disk "$dest")"
    fi
}


# `disk_common` is a copy of `disk_base` with additional software and
# configuration that's common to both the host and the guest.  It's also
# cleaned and trimmed to reduce its compressed size.

do_img_common() {
    # Copy instead of using `derive_image` so `fstrim` can trim the combine
    # base+common image.  `fstrim` can only trim the final read-write image
    # in a backing chain.
    edo cp -v "$(disk base)" "$(disk common).orig"

    # Prepare storage for the custom packages and the extracted kernel and
    # initrd images.
    tar_file=$(mktemp "$(pwd)/kernel.XXXXXX.tar")
    edo dd if=/dev/zero of="$tar_file" bs=1M count=256

    tar_inputs=(
        # linux-pkvm kernel
        "$(find_linux_image_deb ${pkvm_version} pkvm ${pkvm_rev})"
        # opensut_boot
        "$(sole_file ../vm_runner/verse-opensut-boot_[0-9]*_arm64.deb)"
        # vhost-device
        "$(sole_file vhost-device/verse-vhost-device-gpio_[0-9]*_arm64.deb)"
        #"$(sole_file vhost-device/verse-vhost-device-i2c_[0-9]*_arm64.deb)"
        # Could add more packages if needed, e.g. linux-headers
    )
    edo tar --transform='s:.*/::g' -c "${tar_inputs[@]}" | edo dd of="$tar_file" conv=notrunc

    edo bash run_vm_script.sh "$(disk common).orig" vm_scripts/setup_common.sh "$tar_file"

    edo mkdir -p vms/pkvm-boot
    edo tar -C vms/pkvm-boot -xf "$tar_file"
    edo rm -f "$tar_file"
}
define_image_readonly common


# `disk_host` and `disk_guest` is a delta on top of `disk_common` with host-
# or guest-specific software.

do_img_host() {
    edo derive_image "$(disk common)" "$(disk host).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk host).orig"

    tar_file=$(mktemp "$(pwd)/host.XXXXXX.tar")
    tar_inputs=(
        # qemu-system-arm and dependencies
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-arm_*-9999+verse*_arm64.deb)"
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-common_*-9999+verse*_arm64.deb)"
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-data_*-9999+verse*_all.deb)"
    )
    edo tar --transform='s:.*/::g' -cf "$tar_file" "${tar_inputs[@]}"

    edo bash run_vm_script.sh "$(disk host).orig" vm_scripts/setup_host.sh "$tar_file"

    edo rm -f "$tar_file"
}
define_image host

do_img_guest() {
    edo derive_image "$(disk common)" "$(disk guest).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk guest).orig"
    edo bash run_vm_script.sh "$(disk guest).orig" vm_scripts/setup_guest.sh
}
define_image guest


# `disk_host_dev` and `disk_guest_dev` are copies of `disk_host` and
# `disk_guest`.  They aren't deltas backed by `disk_host`/`disk_guest` because
# those images might change (e.g. adding new log entries each time the VM is
# booted).

define_image_copy host host_dev
define_image_copy guest guest_dev
