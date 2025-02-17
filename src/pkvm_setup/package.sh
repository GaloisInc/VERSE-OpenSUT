#!/bin/bash
set -euo pipefail


# Script for managing expensive build artifacts, such as VM images.  The goal
# is to enable caching of these artifacts while ensuring that only up-to-date
# versions of the artifacts are used.  The general idea is to save the output
# of each build step in a tarball named according to the hash of the inputs,
# which can then be cached in Artifactory or in the Github Actions cache.  As
# long as the inputs remain unchanged, later build steps can fetch and unpack
# the tarball to avoid an expensive rebuild.  Artifacts are unpacked into the
# same locations in the source tree where they would normally be produced, so
# build scripts don't need to check different paths when this script is used.


# Helpers

is_function() {
    [[ "$(type -t "$1")" == "function" ]]
}

check_pkg_func() {
    local pkg="$1"
    local func="$2"
    if ! is_function "${pkg}_${func}"; then
        echo "package $pkg does not support $func" 1>&2
        return 1
    fi
}

sole() {
    if [[ "$#" -ne 1 ]]; then
        echo "Error: got multiple results: $*" 1>&2
        return 1
    else
        echo "$1"
    fi
}

edo() {
    echo " >> $*" 1>&2
    "$@"
}


# vm_runner

vm_runner_get_input_hashes() {
    ( cd src/vm_runner && git rev-parse HEAD:./ )
}

vm_runner_build() {
    (
        cd src/vm_runner
        cargo build --release --target aarch64-unknown-linux-gnu
        bash build_deb.sh
    )
}

vm_runner_list_outputs() {
    local deb
    deb="$(sole src/vm_runner/verse-opensut-boot_*_arm64.deb)"
    echo "$deb"
    echo "${deb%.deb}.opensut_boot.measure.txt"
}


# libgpiod

libgpiod_get_input_hashes() {
    ( cd src/pkvm_setup/libgpiod && git rev-parse HEAD:./ )
    sha1sum src/pkvm_setup/build_libgpiod.sh
}

libgpiod_build() {
    (
        cd src/pkvm_setup
        bash build_libgpiod.sh
        bash build_libgpiod.sh aarch64
    )
}

libgpiod_list_outputs() {
    echo src/pkvm_setup/libgpiod/build/lib/.libs/
    echo src/pkvm_setup/libgpiod/build.aarch64/lib/.libs/
}


# vhost_device

vhost_device_get_input_hashes() {
    ( cd src/pkvm_setup/vhost-device && git rev-parse HEAD:./ )
    sha1sum src/pkvm_setup/build_vhost_device.sh
}

vhost_device_dependencies() {
    echo libgpiod
}

vhost_device_build() {
    (
        cd src/pkvm_setup
        bash build_vhost_device.sh
        bash build_vhost_device.sh aarch64
    )
}

vhost_device_list_outputs() {
    sole src/pkvm_setup/vhost-device/verse-vhost-device-gpio_*_arm64.deb
    echo src/pkvm_setup/vhost-device/target/release/vhost-device-gpio
}


# pkvm

pkvm_get_input_hashes() {
    ( cd src/pkvm_setup/linux-pkvm && git rev-parse HEAD:./ )
    sha1sum src/pkvm_setup/build_pkvm.sh
}

pkvm_build() {
    (
        cd src/pkvm_setup
        bash build_pkvm.sh
    )
}

pkvm_list_outputs() {
    for name in linux-headers linux-image; do
        # Match `6.4.0-pkvm-g111122223333` but not `-pkvm-verif-` or `-dbg`
        # variants.
        sole src/pkvm_setup/$name-*-pkvm-g????????????_*_arm64.deb
    done
}


# qemu

qemu_get_input_hashes() {
    ( cd src/pkvm_setup/qemu && git rev-parse HEAD:./ )
    sha1sum src/pkvm_setup/build_qemu.sh
}

qemu_build() {
    (
        cd src/pkvm_setup
        bash build_qemu.sh aarch64
    )
}

qemu_list_outputs() {
    for name in qemu-system-{arm,common,misc} qemu-utils; do
        sole src/pkvm_setup/qemu_build/bookworm-arm64_result/"${name}"_*_arm64.deb
    done
    for name in qemu-system-data; do
        sole src/pkvm_setup/qemu_build/bookworm-arm64_result/"${name}"_*_all.deb
    done
}


# mps

mps_get_input_hashes() {
    ( cd components/mission_protection_system/ && git rev-parse HEAD:./ )
}

mps_dependencies() {
    echo libgpiod
}

mps_build() {
    (
        cd components/mission_protection_system/src/
        make clean
        make mps_bottom CONFIG=self_test
        make mps CONFIG=self_test
        make mps CONFIG=no_self_test
        make mps CONFIG=self_test TARGET=aarch64
        make mps CONFIG=no_self_test TARGET=aarch64
    )
}

mps_list_outputs() {
    echo components/mission_protection_system/src/mps_bottom.self_test
    echo components/mission_protection_system/src/mps.self_test
    echo components/mission_protection_system/src/mps.no_self_test
    echo components/mission_protection_system/src/mps.self_test.aarch64
    echo components/mission_protection_system/src/mps.no_self_test.aarch64
}


# vm_image_base

vm_image_base_get_input_hashes() {
    (
        cd src/pkvm_setup
        sha1sum create_disk_image_base.sh
    )
    ( cd src/pkvm_setup/debian_image && git rev-parse HEAD:./ )
}

vm_image_base_build() {
    (
        cd src/pkvm_setup
        bash create_disk_image_base.sh
    )
}

vm_image_base_list_outputs() {
    echo src/pkvm_setup/vms/disk_base.img
    echo src/pkvm_setup/vms/debian-boot/vmlinuz
    echo src/pkvm_setup/vms/debian-boot/initrd.img
}


# vm_images

vm_images_get_input_hashes() {
    (
        cd src/pkvm_setup
        sha1sum create_disk_images.sh
        sha1sum run_vm_script.sh
        sha1sum change_uuids.sh
    )
    ( cd src/pkvm_setup/vm_scripts && git rev-parse HEAD:./ )
    ( cd src/pkvm_setup/debian_image && git rev-parse HEAD:./ )
}

vm_images_dependencies() {
    echo vm_image_base
    echo vm_runner
    echo vhost_device
    echo pkvm
    echo qemu
    echo trusted_boot
}

vm_images_build() {
    (
        cd src/pkvm_setup
        bash create_disk_images.sh
    )
}

vm_images_list_outputs() {
    echo src/pkvm_setup/vms/disk_common.img
    echo src/pkvm_setup/vms/disk_common_host.img
    echo src/pkvm_setup/vms/disk_common_guest.img
    echo src/pkvm_setup/vms/disk_host1.img
    echo src/pkvm_setup/vms/disk_guest_mps.img
    echo src/pkvm_setup/vms/disk_guest_ardupilot.img
    echo src/pkvm_setup/vms/disk_guest_mkm.img
    echo src/pkvm_setup/vms/disk_guest_logging.img
    echo src/pkvm_setup/vms/pkvm-boot/vmlinuz
    echo src/pkvm_setup/vms/pkvm-boot/initrd.img
    echo src/pkvm_setup/vms/opensut_boot.measure.txt
}


# ardupilot

ardupilot_get_input_hashes() {
    (
        cd components/autopilot
        sha1sum ardupilot_build.sh
        sha1sum ardupilot_init_submodules.sh
        sha1sum ardupilot_install_deps.sh
    )
    ( cd components/autopilot/ardupilot && git rev-parse HEAD:./ )
}

ardupilot_build() {
    bash components/autopilot/ardupilot_build.sh aarch64
}

ardupilot_list_outputs() {
    echo components/autopilot/ardupilot/build.aarch64/sitl/bin/arduplane
    echo components/autopilot/ardupilot/Tools/autotest/models/plane.parm
}


# trusted_boot

trusted_boot_get_input_hashes() {
    ( cd components/platform_crypto/shave_trusted_boot && git rev-parse HEAD:./ )
}

trusted_boot_build() {
    (
        cd components/platform_crypto/shave_trusted_boot/
        make clean
        make VERBOSE=1
        make VERBOSE=1 TARGET=aarch64
        bash build_deb.sh
    )
}

trusted_boot_list_outputs() {
    echo components/platform_crypto/shave_trusted_boot/trusted_boot
    echo components/platform_crypto/shave_trusted_boot/trusted_boot.aarch64
    sole components/platform_crypto/shave_trusted_boot/verse-trusted-boot_*_arm64.deb
}


# logging

logging_get_input_hashes() {
    ( cd components/logging && git rev-parse HEAD:./ )
    ( cd components/autopilot/ardupilot/modules/mavlink && git rev-parse HEAD:./ )
}

logging_build() {
    (
        cd components/logging/
        make clean
        make
        make TARGET=aarch64
    )
}

logging_list_outputs() {
    echo components/logging/logging
    echo components/logging/logging.aarch64
}


# Actions.  Each `do_foo` function can be called via `bash package.sh foo
# package_name`.

# List dependencies of a package to stdout.  Prints nothing if the package
# doesn't define a `foo_dependencies` function.
list_deps() {
    local pkg="$1"
    if is_function "${pkg}_dependencies"; then
        "${pkg}_dependencies"
    fi
}

do_hash_inputs() {
    local pkg="$1"
    check_pkg_func "$pkg" get_input_hashes
    (
        "${pkg}_get_input_hashes"
        for dep in $(list_deps "$pkg"); do
            do_hash_inputs "$dep"
        done
    ) | sha1sum | cut -d' ' -f1
}

do_cache_key() {
    local pkg="$1"
    local input_hash
    input_hash="$(do_hash_inputs "$pkg")"
    echo "$pkg-$input_hash"
}

tarball_path() {
    local pkg="$1"
    echo "packages/$(do_cache_key "$pkg").tar.gz"
}

do_unpack_deps() {
    local pkg="$1"
    for dep in $(list_deps "$pkg"); do
        local src
        src="$(tarball_path "$dep")"
        echo "unpacking $src"
        tar -xvf "$src"
    done
}

do_build() {
    local pkg="$1"
    check_pkg_func "$pkg" build
    "${pkg}_build"
}

do_package() {
    local pkg="$1"
    check_pkg_func "$pkg" list_outputs
    mkdir -p packages
    local dest
    dest="$(tarball_path "$pkg")"
    local inputs
    # Using `mapfile` here means `list_outputs` must print one output per line.
    mapfile -t inputs < <("${pkg}_list_outputs")
    tar -czvf "$dest" "${inputs[@]}"
    echo "packaged $dest"
}

do_check_deps() {
    local pkg="$1"
    for dep in $(list_deps "$pkg"); do
        check_pkg_func "$dep" list_outputs
        local dep_outputs
        dep_outputs="$("${dep}_list_outputs")"
        for file in $dep_outputs; do
            if ! [ -e "$file" ]; then
                echo "missing file $file from dependency $dep of $pkg" 1>&2
                return 1
            fi
        done
    done
}

do_full_build() {
    local pkg="$1"
    do_unpack_deps "$pkg"
    do_check_deps "$pkg"
    do_build "$pkg"
    do_package "$pkg"
}

do_upload() {
    local pkg="$1"
    shift 1
    local tarball
    tarball="$(tarball_path "$pkg")"
    # Remaining arguments are passed through to curl.  Typically these will be
    # authentication options like `-u USERNAME`.
    edo curl "$@" -T "$tarball" \
        "https://artifactory.galois.com/artifactory/rde_generic-local/verse-opensut/$(basename "$tarball")"
}

do_download() {
    local pkg="$1"
    shift 1
    local tarball
    tarball="$(tarball_path "$pkg")"
    # Remaining arguments are passed through to curl.  Typically these will be
    # authentication options like `-u USERNAME`.
    mkdir -p "$(dirname "$tarball")"
    edo curl "$@" -o "$tarball" --fail-with-body \
        "https://artifactory.galois.com/artifactory/rde_generic-local/verse-opensut/$(basename "$tarball")"
}

script_dir="$(dirname "$0")"
root_dir="$(cd "$script_dir" && git rev-parse --show-toplevel)"
cd "$root_dir"

action="$1"
pkg="$2"
shift 2

if ! is_function "do_$action"; then
    echo "unknown action $action" 1>&2
    exit 1
fi
"do_$action" "$pkg" "$@"
