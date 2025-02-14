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
#   * common_host
#     * host1
#     * host_dev
#   * common_guest
#     * guest_mps
#     * guest_dev
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


# `common` is a copy of `base` with additional software and configuration
# that's common to both the host and the guest.  It's also cleaned and trimmed
# to reduce its compressed size.

do_img_common() {
    # Copy instead of using `derive_image` so `fstrim` can trim the combine
    # base+common image.  `fstrim` can only trim the final read-write image
    # in a backing chain.
    edo cp -v "$(disk base)" "$(disk common).orig"

    # Prepare storage for the custom packages and the extracted kernel and
    # initrd images.
    tar_file=$(mktemp "$(pwd)/kernel.XXXXXX.tar")
    edo dd if=/dev/zero of="$tar_file" bs=1M count=256

    local opensut_boot_deb
    opensut_boot_deb="$(sole_file ../vm_runner/verse-opensut-boot_[0-9]*_arm64.deb)"
    local opensut_boot_measure="${opensut_boot_deb%.deb}.opensut_boot.measure.txt"

    tar_inputs=(
        # linux-pkvm kernel
        "$(find_linux_image_deb ${pkvm_version} pkvm ${pkvm_rev})"
        # opensut_boot
        "${opensut_boot_deb}"
        # trusted_boot
        "$(sole_file ../../components/platform_crypto/shave_trusted_boot/verse-trusted-boot_[0-9]*_arm64.deb)"
        # Could add more packages if needed, e.g. linux-headers
    )
    edo tar --transform='s:.*/::g' -c "${tar_inputs[@]}" | edo dd of="$tar_file" conv=notrunc

    edo bash run_vm_script.sh "$(disk common).orig" vm_scripts/setup_common.sh "$tar_file"

    edo mkdir -p vms/pkvm-boot
    edo tar -C vms/pkvm-boot -xf "$tar_file"
    edo rm -f "$tar_file"

    # Take the measure of the `opensut_boot` binary that was included in the
    # image and save it alongside the image itself, so it's easy to find.
    edo cp -v "${opensut_boot_measure}" vms/opensut_boot.measure.txt
}
define_image_readonly common


# `common_host` and `common_guest` are deltas on top of `common` with host- or
# guest-specific software.

do_img_common_host() {
    edo derive_image "$(disk common)" "$(disk common_host).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk common_host).orig"

    tar_file=$(mktemp "$(pwd)/host.XXXXXX.tar")
    tar_inputs=(
        # qemu-system-arm and dependencies
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-arm_*-9999+verse*_arm64.deb)"
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-common_*-9999+verse*_arm64.deb)"
        "$(sole_file qemu_build/bookworm-arm64_result/qemu-system-data_*-9999+verse*_all.deb)"
        # vhost-device
        "$(sole_file vhost-device/verse-vhost-device-gpio_[0-9]*_arm64.deb)"
        #"$(sole_file vhost-device/verse-vhost-device-i2c_[0-9]*_arm64.deb)"
    )
    edo tar --transform='s:.*/::g' -cf "$tar_file" "${tar_inputs[@]}"

    edo bash run_vm_script.sh "$(disk common_host).orig" vm_scripts/setup_common_host.sh "$tar_file"

    edo rm -f "$tar_file"
}
define_image_readonly common_host

do_img_common_guest() {
    edo derive_image "$(disk common)" "$(disk common_guest).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk common_guest).orig"
    edo bash run_vm_script.sh "$(disk common_guest).orig" vm_scripts/setup_common_guest.sh
}
define_image_readonly common_guest


# Network address assignment:
#
# All VMs that make up the OpenSUT (both hosts and guests) are connected with a
# single virtual network, so they must all have distinct IP and MAC addresses.
# We currently assign addresses as follows:
#
# * IP address: Each VM is assigned `10.0.2.1XY/24`, where `X` is 1 for host
# VMs and 2 for guest VMs, and `Y` is a single digit identifying a particular
# host/guest VM.  The default gateway for all VMs is `10.0.2.2`; this is a
# gateway provided by QEMU's `-netdev user` networking mode.
#
# * MAC addresses: A VM may have multiple network interfaces, each of which
#   needs a separate MAC address.  We assign addresses `00:50:56:0X:0Y:ZZ`,
#   where `X` and `Y` are the same as for the VM's IP address, and `ZZ`
#   identifies the network interface.  For normal virtual network interfaces of
#   the form `enp0s<N>`, `ZZ` is `0N`, and for the bridge interface `br0`, `ZZ`
#   is `ff`.  For example, `enp0s4` on guest #1 is given `00:50:56:02:01:04`.
#
# For MAC addresses, we use the range `00:50:56:00:00:00` through
# `00:50:56:3f:ff:ff` because it's reserved by VMware for assigning custom MAC
# addresses to VMs, and thus shouldn't conflict with anything that's assigned
# automatically by QEMU or Linux.

do_img_host1() {
    edo derive_image "$(disk common_host)" "$(disk host1).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk host1).orig"
    edo bash run_vm_script.sh "$(disk host1).orig" vm_scripts/setup_host1.sh
}
define_image host1
# * IP: 10.0.2.111
# * MACs: 00:50:56:01:01:04, :05, :ff

do_img_guest_mps() {
    edo derive_image "$(disk common_guest)" "$(disk guest_mps).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk guest_mps).orig"
    edo bash run_vm_script.sh "$(disk guest_mps).orig" vm_scripts/setup_guest_mps.sh
}
define_image guest_mps
# * IP: 10.0.2.121
# * MAC: 00:50:56:02:01:04

do_img_guest_ardupilot() {
    edo derive_image "$(disk common_guest)" "$(disk guest_ardupilot).orig"
    edo bash change_uuids.sh "$(disk common)" "$(disk guest_ardupilot).orig"
    edo bash run_vm_script.sh "$(disk guest_ardupilot).orig" vm_scripts/setup_guest_ardupilot.sh
}
define_image guest_ardupilot
# * IP: 10.0.2.122
# * MAC: 00:50:56:02:02:04

# How to add a new disk image:
#
# 1. Copy the `host1` or `guest_mps` block in this script, and update the image
#    name throughout (e.g. change all instances of `host1` to `host2` in the
#    new copy).
# 2. Create a setup script for the new image by copying the existing one (e.g.
#    `cp vm_scripts/setup_host1.sh vm_scripts/setup_host2.sh`).
# 3. Update the hostname in the setup script to match the new image name.
# 4. Edit the network part of the setup script to assign new, non-conflicting
#    IP and MAC addresses.
# 5. Customize the setup script as needed, such as by installing additional
#    Debian packages required by the new application.


# We make "dev" copies of some VMs for local development use.  These can be
# modified as needed for testing or experimentation without affecting the
# images that are used for automated tests.
define_image_copy host1 host_dev
define_image_copy guest_mps guest_dev
