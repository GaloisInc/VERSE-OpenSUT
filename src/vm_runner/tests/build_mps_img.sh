#!/bin/bash
set -euo pipefail

tests_dir="$(dirname "$0")"

python3 "$tests_dir/../build_application_image.py" \
    -f "$tests_dir/mps_guest.toml=runner.toml" \
    -f "$tests_dir/../../../components/mission_protection_system/src/rts=mps" \
    -f "$tests_dir/mps.sh" \
    -o "$tests_dir/mps_guest.img"

python3 "$tests_dir/../build_application_image.py" \
    -f "$tests_dir/mps_host.toml=runner.toml" \
    -f "$tests_dir/mps_guest.img" \
    -o "$tests_dir/mps_host.img"

