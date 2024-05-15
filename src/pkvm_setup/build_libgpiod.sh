#!/bin/bash
set -euo pipefail

# Dependencies: build-essential, autoconf, automake, autoconf-archive

cd libgpiod
./autogen.sh
make -j "$(nproc)"
