#!/bin/bash
set -euo pipefail

# Dependencies:
# - A recent Rust stable toolchain (tested with 1.78.0)
# - libgpiod (run `build_libgpiod.sh` first)
#
# Additional dependencies for aarch64 cross-builds:
# - The Rust toolchain must support the aarch64-unknown-linux-gnu target

target=
if [[ "$#" -ne 0 ]]; then
    target="$1"
fi

gpiod_build_dir=build
if [[ -n "$target" ]]; then
    gpiod_build_dir="$gpiod_build_dir.$target"
fi

cargo_args=(
    --release
)
case "$target" in
    aarch64)
        cargo_args+=(
            --target aarch64-unknown-linux-gnu
        )
        ;;
esac

if ! [[ -f libgpiod/$gpiod_build_dir/lib/.libs/libgpiod.so ]] \
        && ! [[ -f libgpiod/$gpiod_build_dir/lib/.libs/libgpiod.a ]]; then
    echo 'missing libgpiod.so / libgpiod.a; run build_libgpiod.sh first' 1>&2
    exit 1
fi

pwd="$(pwd)"
export SYSTEM_DEPS_LIBGPIOD_NO_PKG_CONFIG=1
export SYSTEM_DEPS_LIBGPIOD_SEARCH_NATIVE="$pwd/libgpiod/$gpiod_build_dir/lib/.libs/"
export SYSTEM_DEPS_LIBGPIOD_LIB=gpiod
# libgpiod doesn't have generated headers, so we can just point to the include
# dir in the source tree.
export SYSTEM_DEPS_LIBGPIOD_INCLUDE="$pwd/libgpiod/include/"

cd vhost-device

# If rustup is installed, this will cause it to use the stable toolchain (if
# the caller hasn't already set `RUSTUP_TOOLCHAIN` to somtehing else).  Without
# rustup, this does nothing.
: "${RUSTUP_TOOLCHAIN=stable}"
export RUSTUP_TOOLCHAIN

cargo build --bin vhost-device-gpio "${cargo_args[@]}"
#cargo build --bin vhost-device-i2c "${cargo_args[@]}"
