#!/bin/bash
set -euo pipefail

input="$1"
preseed="$2"
output="$3"
shift 3

cp "$input" "$output"

mkdir -p work
(
    cp "$preseed" work/preseed.cfg
    cd work
    echo "./preseed.cfg" | cpio -H newc -o | gzip
    rm preseed.cfg
) >> "$output"
rmdir work 2>/dev/null || true
