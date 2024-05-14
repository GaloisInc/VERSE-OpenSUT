#!/bin/bash
set -euo pipefail

mkdir -p vms/pkvm-boot

cd linux-pkvm
make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j "$(nproc)" defconfig

# Enable virtio GPIO and I2C drivers.  We pass these through from outside to
# the host VM and then through to some of the guests, so the host needs the
# drivers.
./scripts/config -e CONFIG_GPIO_VIRTIO
./scripts/config -e CONFIG_I2C_VIRTIO

make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j "$(nproc)" Image
cp -v arch/arm64/boot/Image ../vms/pkvm-boot/vmlinuz-pkvm