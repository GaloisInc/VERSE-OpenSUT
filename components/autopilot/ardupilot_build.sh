#!/bin/bash
set -euo pipefail

# Build the ArduPilot SITL binary for aarch64.

target=
if [[ "$#" -ne 0 ]]; then
    target="$1"
fi

build_dir=build
if [[ -n "$target" ]]; then
    build_dir="$build_dir.$target"
fi

cd "$(dirname "$0")/ardupilot"

edo() {
    echo " >> $*" 1>&2
    "$@"
}

case "$target" in
    aarch64)
        export CC=aarch64-linux-gnu-gcc
        export CXX=aarch64-linux-gnu-g++
        export LD=aarch64-linux-gnu-g++
        ;;
esac

. venv/bin/activate
./waf -o "${build_dir}" configure --board sitl
./waf -o "${build_dir}" build --target bin/arduplane
