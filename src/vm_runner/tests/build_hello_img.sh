#!/bin/bash
set -euo pipefail

tests_dir="$(dirname "$0")"

python3 "$tests_dir/../build_application_image.py" \
    -f "$tests_dir/hello.sh" \
    -f "$tests_dir/hello.toml=runner.toml" \
    -o "$tests_dir/hello.img"
