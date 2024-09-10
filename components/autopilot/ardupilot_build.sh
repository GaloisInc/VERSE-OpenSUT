#!/bin/bash
set -euo pipefail

# Build the ArduPilot SITL binary for aarch64.

cd "$(dirname "$0")/ardupilot"

edo() {
    echo " >> $*" 1>&2
    "$@"
}

. venv/bin/activate
export CC=aarch64-linux-gnu-gcc
export CXX=aarch64-linux-gnu-g++
export LD=aarch64-linux-gnu-g++
./waf -o build.aarch64 configure --board sitl
./waf -o build.aarch64 build --target bin/arduplane
