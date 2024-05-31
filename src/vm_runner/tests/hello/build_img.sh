#!/bin/bash
set -euo pipefail

hello_dir="$(dirname "$0")"

python3 "$hello_dir/../../build_application_image.py" \
    -f "$hello_dir/guest.toml=runner.toml" \
    -f "$hello_dir/hello.sh" \
    -o "$hello_dir/guest.img"

python3 "$hello_dir/../../build_application_image.py" \
    -f "$hello_dir/host.toml=runner.toml" \
    -f "$hello_dir/guest.img" \
    -o "$hello_dir/host.img"

