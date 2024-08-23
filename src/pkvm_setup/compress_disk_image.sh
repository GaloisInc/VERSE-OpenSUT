#!/bin/bash
set -euo pipefail

# Usage: bash compress_disk_image.sh src.img dest.img
#
# Compress QEMU image `src.img` and write the compressed version to `dest.img`.

edo() {
    echo " >> $*" 1>&2
    "$@"
}

get_img_info() {
    qemu-img info --output=json "$1" | jq -r -e ".\"$2\""
}

src="$1"
dest="$2"
shift 2

qemu_args=( -c -O qcow2 )
if backing="$(get_img_info "$src" backing-filename)"; then
    if backing_format="$(get_img_info "$src" backing-filename-format)"; then
        qemu_args+=( -B "$backing" -F "$backing_format" )
    else
        echo "error: image $src has backing-filename but no backing-filename-format" 1>&2
        exit 1
    fi
fi
edo qemu-img convert "${qemu_args[@]}" "$src" "$dest"
