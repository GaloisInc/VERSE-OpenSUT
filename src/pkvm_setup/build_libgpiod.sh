#!/bin/bash
set -euo pipefail

# Dependencies: build-essential, autoconf, automake, autoconf-archive
#
# Additional dependencies for aarch64 cross-builds: gcc-aarch64-linux-gnu

target=
if [[ "$#" -ne 0 ]]; then
    target="$1"
fi

build_dir=build
if [[ -n "$target" ]]; then
    build_dir="$build_dir.$target"
fi

configure_args=()
case "$target" in
    aarch64)
        configure_args+=(
            --host aarch64-unknown-linux-gnu
            # We use `--disable-shared` here so that `vhost-device` will be
            # forced to statically link libgpiod.  This means one less
            # dependency to worry about when installing into the VM.
            #
            # (Also, cross-compiling with `--enable-shared` doesn't seem to
            # actually produce a shared version of the library, only a few
            # broken symlinks.)
            --disable-shared
            CC=aarch64-linux-gnu-gcc
            LD=aarch64-linux-gnu-gcc
        )
        ;;
esac

cd libgpiod
mkdir -p "$build_dir"
cd "$build_dir"
# For some reason, doing ./autogen.sh and ./configure as separate steps in an
# out-of-tree build causes ./configure to complain that the source tree is
# already configured.
../autogen.sh "${configure_args[@]}"
make -j "$(nproc)"
