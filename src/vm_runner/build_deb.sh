#!/bin/bash
set -euo pipefail

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

boot_bin=target/aarch64-unknown-linux-gnu/release/opensut_boot
check_bin "$boot_bin"
runner_bin=target/aarch64-unknown-linux-gnu/release/opensut_vm_runner
check_bin "$runner_bin"

image=$(mktemp -d)
edo mkdir -p "$image/opt/opensut/bin"
edo cp -v "$boot_bin" "$image/opt/opensut/bin/"
edo cp -v "$runner_bin" "$image/opt/opensut/bin/"

cargo_version="$(cargo read-manifest | \
    python3 -c 'import json, sys; print(json.load(sys.stdin)["version"])')"
git_rev="$(git rev-parse HEAD | cut -c -8)"
version="${cargo_version}-g${git_rev}"

size=$(( ( "$(stat -c %s "$boot_bin")" + 1023) / 1024  ))

edo mkdir -p "$image/DEBIAN"
edo tee "$image/DEBIAN/control" <<EOF
Package: verse-opensut-boot
Version: $version
Architecture: arm64
Maintainer: Stuart Pernsteiner <spernsteiner@galois.com>
Depends: libc6
Installed-Size: $size
Homepage: https://github.com/GaloisInc/VERSE-OpenSUT/tree/main/src/vm_runner
Description: VERSE OpenSUT boot-time agent
 opensut_boot is run at boot time in OpenSUT VMs to start up sub-VMs or other
 services.
EOF

systemd_dir="$image/usr/lib/systemd/system"
edo mkdir -p "$systemd_dir"
edo cp -v opensut-boot.service "$systemd_dir"
edo cp -v opensut-boot.target "$systemd_dir"
edo cp -v opensut-trusted-boot.service "$systemd_dir"
edo cp -v opensut-trusted-boot.target "$systemd_dir"

edo dpkg-deb --root-owner-group --build "$image" "verse-opensut-boot_${version}-1_arm64.deb"

edo rm -rf "$image"
