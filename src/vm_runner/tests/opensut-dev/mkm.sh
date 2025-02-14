#!/bin/bash
set -euo pipefail

mkm_bin="$(dirname "$0")/mkm"
sha256sum "$mkm_bin"

export MKM_BIND_ADDR=10.0.2.123

echo "Starting mkm"
"$mkm_bin" mkm_config.bin
echo "mkm exited with code $?"
