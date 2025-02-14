#!/bin/bash
set -euo pipefail

script_dir="$(dirname "$0")"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/guest_mps.toml=runner.toml" \
    -f "$script_dir/../../../../components/mission_protection_system/src/mps.no_self_test.aarch64=mps" \
    -f "$script_dir/mps.sh" \
    -o "$script_dir/guest_mps.img"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/guest_ardupilot.toml=runner.toml" \
    -f "$script_dir/../../../../components/autopilot/ardupilot/build.aarch64/sitl/bin/arduplane" \
    -f "$script_dir/ardupilot.sh" \
    -f "$script_dir/plane-jsbsim-ext.parm" \
    -o "$script_dir/guest_ardupilot.img"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/guest_logging.toml=runner.toml" \
    -f "$script_dir/../../../../components/logging/logging.aarch64=logging" \
    -f "$script_dir/../../../../components/mkm_client/mkm_client.aarch64=mkm_client" \
    -f "$script_dir/../../../../components/logging/logging_boot.sh=logging.sh" \
    -f "$script_dir/logging_config.sh" \
    -o "$script_dir/guest_logging.img"

# Generate MKM config
measure_logging="$(
    python3 "$script_dir/../../../../components/platform_crypto/shave_trusted_boot/calc_measure.py" \
        --set "$(cat "$script_dir/../../../../src/pkvm_setup/vms/opensut_boot.measure.txt")" \
        --measure-hash-of-file "$script_dir/guest_logging.img" \
        | head -n 1
)"
cat >"$script_dir/mkm_config.ini" <<EOF
[${measure_logging}]
key0 = 6e79d128effe911273bceb4df884021b63f8d0f81a4d80db90ec5d4ffa8fca9b
EOF
python3 "$script_dir/../../../../components/mission_key_management/convert_config.py" \
    "$script_dir/mkm_config.ini" "$script_dir/mkm_config.bin"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/guest_mkm.toml=runner.toml" \
    -f "$script_dir/../../../../components/mission_key_management/mkm.aarch64=mkm" \
    -f "$script_dir/mkm.sh" \
    -f "$script_dir/mkm_config.bin" \
    -o "$script_dir/guest_mkm.img"

python3 "$script_dir/../../build_application_image.py" \
    -f "$script_dir/host.toml=runner.toml" \
    -f "$script_dir/guest_mps.img" \
    -f "$script_dir/guest_ardupilot.img" \
    -f "$script_dir/guest_mkm.img" \
    -f "$script_dir/guest_logging.img" \
    -o "$script_dir/host.img"
