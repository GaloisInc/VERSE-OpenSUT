#!/bin/bash
set -euo pipefail

script_dir="$(dirname "$0")"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/guest.toml=runner.toml" \
    -f "$script_dir/../../../../components/autopilot/ardupilot/build.aarch64/sitl/bin/arduplane" \
    -f "$script_dir/ardupilot.sh" \
    -f "$script_dir/plane-jsbsim-ext.parm" \
    -o "$script_dir/guest.img"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/host.toml=runner.toml" \
    -f "$script_dir/guest.img" \
    -o "$script_dir/host.img"

