#!/bin/bash
set -euo pipefail

mps_dir="$(dirname "$0")"

python3 "$mps_dir/../../build_application_image.py" \
    -f "$mps_dir/guest.toml=runner.toml" \
    -f "$mps_dir/../../../../components/mission_protection_system/src/mps.no_self_test.aarch64=mps" \
    -f "$mps_dir/mps.sh" \
    -o "$mps_dir/guest.img"

python3 "$mps_dir/../../build_application_image.py" \
    -f "$mps_dir/host.toml=runner.toml" \
    -f "$mps_dir/guest.img" \
    -o "$mps_dir/host.img"

