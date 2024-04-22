#!bin/bash
set -euo pipefail

cd linux-pkvm
make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) defconfig
make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) Image
cp -v arch/arm64/boot/Image ../vmlinuz-pkvm
