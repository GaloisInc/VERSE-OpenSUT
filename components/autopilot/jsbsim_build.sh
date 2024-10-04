#!/bin/bash
set -euo pipefail

# Build the JSBSim binary.

build_dir=build

cd "$(dirname "$0")/jsbsim"

edo() {
    echo " >> $*" 1>&2
    "$@"
}

edo mkdir -p "$build_dir"
cd "$build_dir"
edo cmake .. -DCMAKE_BUILD_TYPE=Release
edo make -j"$(nproc)"
