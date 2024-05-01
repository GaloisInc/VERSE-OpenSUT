#!/bin/bash
set -euo pipefail

# Helper for use with `copy_file.sh`.  This reads the file from `/dev/vdc` and
# copies it to the desired location under `/home/user`.

dest=$1
size=$2
shift 1

cd ~user
head -c $size /dev/vdc >"$dest"
chown -v user:user "$dest"
