#!/bin/bash
set -euo pipefail

# Helper for use with `copy_file.sh`.  This reads the file from `/dev/vdc` and
# copies it to the desired location under `/home/user`.

dest=$1
size=$2
mode=$3
shift 3

cd ~user
head -c "$size" /dev/vdc >"$dest"
sha256sum "$dest"
chown -v user:user "$dest"
chmod -v "$mode" "$dest"
