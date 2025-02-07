#!/bin/bash
set -euo pipefail

package_version=0.0.1

edo() {
    echo " >> $*" 1>&2
    "$@"
}

check_bin() {
    local bin="$1"
    if ! [[ -f "$bin" ]]; then
        echo "Error: $bin not found; build it first" 1>&2
        exit 1
    else
        age=$(( "$(date +%s)" - "$(stat -c %Y "$bin")" ))
        age_hr=$(( age / 3600 ))
        age_min=$(( age / 60 % 60 ))
        age_sec=$(( age % 60 ))
        age_str=$(printf %dh%02dm%02ds "$age_hr" "$age_min" "$age_sec")
        echo "Using $bin (built $age_str ago)"
    fi
}

trusted_boot_bin=./trusted_boot.aarch64
check_bin "$trusted_boot_bin"

image=$(mktemp -d)
edo mkdir -p "$image/opt/opensut/bin"
edo cp -v "$trusted_boot_bin" "$image/opt/opensut/bin/trusted_boot"

git_rev="$(git rev-parse HEAD | cut -c -8)"
version="${package_version}-g${git_rev}"

size=$(( ( "$(stat -c %s "$trusted_boot_bin")" + 1023) / 1024  ))

edo mkdir -p "$image/DEBIAN"
edo tee "$image/DEBIAN/control" <<EOF
Package: verse-trusted-boot
Version: $version
Architecture: arm64
Maintainer: Stuart Pernsteiner <spernsteiner@galois.com>
Depends: libc6
Installed-Size: $size
Homepage: https://github.com/GaloisInc/VERSE-OpenSUT/tree/main/components/platform_crypto/shave_trusted_boot
Description: VERSE OpenSUT trusted boot agent
 trusted_boot runs at boot time within each VM to provide attestation services
 to other processes in the VM.
EOF

edo dpkg-deb --root-owner-group --build "$image" "verse-trusted-boot_${version}-1_arm64.deb"

edo rm -rf "$image"
