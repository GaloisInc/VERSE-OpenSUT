#!/bin/bash
set -euo pipefail

mps_bin="$(dirname "$0")/mps"
sha256sum "$mps_bin"
echo "Starting mps"
setsid -c "$mps_bin" </dev/hvc0 >/dev/hvc0
echo "mps exited with code $?"
