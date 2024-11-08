# Top Level VERSE OpenSUT Dockerfile
FROM --platform=linux/amd64 debian:bookworm

# Labels added as described in
# https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#labelling-container-images
LABEL org.opencontainers.image.source=https://github.com/GaloisInc/VERSE-OpenSUT
LABEL org.opencontainers.image.description="VERSE-OpenSUT Base Platform Image"
LABEL org.opencontainers.image.licenses=BSD3

# Install dependencies
RUN apt-get clean \
  && apt-get update \
  && apt-get upgrade -y \
  && apt-get install -y \
  # General deps
  curl \
  # Jsbsim proxy /
  # Libgpiod / vhost-device
  build-essential autoconf automake autoconf-archive \
  # Trusted boot
  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  # MPS
  verilator python3-pip clang

# Ardupilot dependencies
ADD components/autopilot/ardupilot_install_deps.sh /tmp/ardupilot_install_deps.sh
RUN BUILD_ONLY=1 bash components/autopilot/ardupilot_install_deps.sh

# Install rustup & pin to 1.74
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o rustup.rs \
  && sh ./rustup.rs -y \
  && . "$HOME/.cargo/env" \
  && rustup toolchain install 1.74 \
  && rustup target add aarch64-unknown-linux-gnu \
  && rustup default 1.74-x86_64-unknown-linux-gnu

# The following deps are needed to build the VM images
# Disk image and qemu dependencies
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
  qemu-system-arm qemu-utils \
  debian-installer-12-netboot-arm64 \
  cpio

# Prepare deb-src
RUN touch /etc/apt/sources.list \
  && echo "deb-src http://deb.debian.org/debian bookworm main contrib non-free" > /etc/apt/sources.list \
  && apt-get update
# Other sources:
# deb-src http://deb.debian.org/debian bookworm-updates main contrib non-free
# deb-src http://deb.debian.org/debian-security bookworm-security main contrib non-free

# Build dependencies for linux-pkvm / linux-pkvm-verif kernel
RUN apt build-dep -y linux

WORKDIR /work
