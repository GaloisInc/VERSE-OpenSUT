#!/bin/bash
set -euo pipefail

mkdir -p vms

disk_base=vms/disk_base.img


edo() {
    echo " >> $*" 1>&2
    "$@"
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
