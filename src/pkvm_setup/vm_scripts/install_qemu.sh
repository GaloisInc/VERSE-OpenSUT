#!/bin/bash
set -euo pipefail

if [[ "$(id -u)" -eq "0" ]]; then
    # Drop privileges for the rest of the script.
    cp "$0" /tmp/vm-script
    chown user:user /tmp/vm-script
    exec sudo -u user /bin/bash /tmp/vm-script "$@"
fi

cd ~

# Install required dependencies listed in QEMU docs
sudo apt install -y build-essential
sudo apt install -y git libglib2.0-dev libfdt-dev libpixman-1-dev zlib1g-dev ninja-build
# Install extra dependencies needed for specific features
sudo apt install -y python3-venv libcap-ng-dev libslirp-dev


git clone https://github.com/qemu/qemu
cd qemu

# QEMU 7.2.9 is the version provided by current Debian Stable.
git checkout v7.2.9

git apply <<EOF
diff --git a/VERSION b/VERSION
index 672f66a613..0289b5afc4 100644
--- a/VERSION
+++ b/VERSION
@@ -1 +1 @@
-7.2.9
+7.2.9.verse1
diff --git a/accel/kvm/kvm-all.c b/accel/kvm/kvm-all.c
index 0a127ece11..a30899ceec 100644
--- a/accel/kvm/kvm-all.c
+++ b/accel/kvm/kvm-all.c
@@ -314,6 +314,7 @@ err:
                      " start=0x%" PRIx64 ", size=0x%" PRIx64 ": %s",
                      __func__, mem.slot, slot->start_addr,
                      (uint64_t)mem.memory_size, strerror(errno));
+       ret = 0; // HACK: crosvm ignore these errors on pkvm, so we do too
     }
     return ret;
 }
EOF

mkdir -p build
cd build

config_args=(
    # We only need `qemu-system-aarch64`, not `qemu-user-*`.
    --enable-system --disable-user --target-list=aarch64-softmmu
    --enable-kvm
    # Enable virtio-9p
    --enable-virtfs
    # Enable `-netdev user` (requires libslirp)
    --enable-slirp
    # Enable vhost-user-gpio and similar devices
    --enable-vhost-user
)
../configure "${config_args[@]}"
make -j "$(nproc)" qemu-system-aarch64
