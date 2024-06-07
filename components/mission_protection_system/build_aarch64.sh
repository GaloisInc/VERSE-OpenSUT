#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")/src"
make clean
make CC=aarch64-linux-gnu-g++ CXX=aarch64-linux-gnu-g++ SENSORS=NotSimulated SELF_TEST=Disabled
cp -v rts rts.no_self_test.aarch64
make clean
make CC=aarch64-linux-gnu-g++ CXX=aarch64-linux-gnu-g++ SENSORS=NotSimulated SELF_TEST=Enabled
cp -v rts rts.self_test.aarch64
