#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

# Build a modified QEMU Debian package with reduced dependencies.

target=
if [[ "$#" -ne 0 ]]; then
    target="$1"
fi
case "$target" in
    # Accept `aarch64` as an alias for the Debian name `arm64`.
    aarch64)
        target="arm64"
        ;;
    # If no target is provided, use the default for this host.
    '')
        target="$(dpkg --print-architecture)"
        ;;
esac

dist=bookworm
echo "target=$target"
echo "dist=$dist"

sudo apt install -y pbuilder ubuntu-dev-tools dpkg-dev pristine-tar
PBUILDFOLDER="$(pwd)/qemu_build"
export PBUILDFOLDER

if [[ -f "$PBUILDFOLDER/${dist}-base.tgz" ]]; then
    echo "Using existing pbuilder base.tgz for $dist $target" 1>&2
else
    echo "Creating pbuilder base.tgz for $dist $target" 1>&2
    pbuilder-dist "$dist" "$target" create
fi

sole() {
    if [[ "$#" -ne 1 ]]; then
        echo "Error: got multiple results: $*" 1>&2
        return 1
    else
        echo "$1"
    fi
}

(
    cd qemu
    echo "Preparing QEMU sources" 1>&2
    pristine-tar checkout ../qemu_9.0.2+ds.orig.tar.xz
    debian/rules debian/control
    dpkg-buildpackage --build=source -uc -us
)

dsc_file="$(sole qemu_*-9999+verse*.dsc)"
pbuilder-dist "$dist" "$target" build "$dsc_file"
