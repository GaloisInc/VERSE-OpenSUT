#!/bin/bash
set -euo pipefail

tests_dir="$(dirname "$0")"

python3 "$tests_dir/../build_application_image.py" \
    -f "$tests_dir/hello_guest.toml=runner.toml" \
    -f "$tests_dir/hello.sh" \
    -o "$tests_dir/hello_guest.img"

python3 "$tests_dir/../build_application_image.py" \
    -f "$tests_dir/hello_host.toml=runner.toml" \
    -f "$tests_dir/hello_guest.img" \
    -o "$tests_dir/hello_host.img"

