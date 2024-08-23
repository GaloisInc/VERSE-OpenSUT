#!/bin/bash
set -euo pipefail

dev_dir="$(dirname "$0")"

python3 "$dev_dir/../../build_application_image.py" \
    -f "$dev_dir/guest.toml=runner.toml" \
    -f "$dev_dir/hello.sh" \
    -o "$dev_dir/guest.img"

python3 "$dev_dir/../../build_application_image.py" \
    -f "$dev_dir/host.toml=runner.toml" \
    -f "$dev_dir/guest.img" \
    -o "$dev_dir/host.img"
