#!/bin/bash
set -euo pipefail

mps_bin="$(dirname "$0")/mps"
sha256sum "$mps_bin"

# `host.toml` runs the guest VM with a virtual GPIO device as /dev/gpiochip1
export MPS_GPIO_DEVICE=/dev/gpiochip1

echo "Starting mps"
setsid -c "$mps_bin" </dev/hvc0 >/dev/hvc0
echo "mps exited with code $?"
