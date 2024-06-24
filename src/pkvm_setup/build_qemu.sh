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

sudo apt install -y pbuilder ubuntu-dev-tools dpkg-dev
PBUILDFOLDER="$(pwd)/qemu_build"
export PBUILDFOLDER

echo "Creating pbuilder base.tgz for $dist $target" 1>&2
pbuilder-dist "$dist" "$target" create

sole() {
    if [[ "$#" -ne 1 ]]; then
        echo "Error: got multiple results: $*" 1>&2
        return 1
    else
        echo "$1"
    fi
}

patch_dir="$(pwd)/qemu_patches"
(
    # TODO: clean old src dir first (avoid reapplying patches)
    mkdir -p "$PBUILDFOLDER/src"
    cd "$PBUILDFOLDER/src"
    echo "Preparing QEMU sources" 1>&2
    apt source qemu
    (
        cd "$(sole qemu*/)"
        for patch in "$patch_dir"/debian-*.patch; do
            echo "Applying $patch" 1>&2
            patch -p1 <"$patch"
        done
        dpkg-buildpackage --build=source -uc -us
    )
)

dsc_file="$(sole "$PBUILDFOLDER/src/"qemu_*-9999+verse*.dsc)"
pbuilder-dist "$dist" "$target" build "$dsc_file"
