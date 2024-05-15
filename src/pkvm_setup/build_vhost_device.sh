#!/bin/bash
set -euo pipefail

# Dependencies:
# - A recent Rust stable toolchain (tested with 1.78.0)
# - libgpiod (run `build_libgpiod.sh` first)

if ! [[ -f libgpiod/lib/.libs/libgpiod.so ]] && ! [[ -f libgpiod/lib/.libs/libgpiod.a ]]; then
    echo 'missing libgpiod.so / libgpiod.a; run build_libgpiod.sh first' 1>&2
    exit 1
fi

pwd="$(pwd)"
export SYSTEM_DEPS_LIBGPIOD_NO_PKG_CONFIG=1
export SYSTEM_DEPS_LIBGPIOD_SEARCH_NATIVE="$pwd/libgpiod/lib/.libs/"
export SYSTEM_DEPS_LIBGPIOD_LIB=gpiod
export SYSTEM_DEPS_LIBGPIOD_INCLUDE="$pwd/libgpiod/include/"

cd vhost-device

# If rustup is installed, this will cause it to use the stable toolchain (if
# the caller hasn't already set `RUSTUP_TOOLCHAIN` to somtehing else).  Without
# rustup, this does nothing.
: "${RUSTUP_TOOLCHAIN=stable}"
export RUSTUP_TOOLCHAIN

cargo build --bin vhost-device-gpio
#cargo build --bin vhost-device-i2c
