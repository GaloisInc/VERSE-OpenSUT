# Top Level VERSE OpenSUT Dockerfile
FROM --platform=linux/amd64 debian:bookworm

# Labels added as described in
# https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#labelling-container-images
LABEL org.opencontainers.image.source=https://github.com/GaloisInc/VERSE-OpenSUT
LABEL org.opencontainers.image.description="VERSE-OpenSUT Base Platform Image"
LABEL org.opencontainers.image.licenses=BSD3

RUN apt-get clean \
  && apt-get update \
  && apt-get upgrade -y

# Prepare deb-src
RUN touch /etc/apt/sources.list \
  && echo "deb-src http://deb.debian.org/debian bookworm main contrib non-free" > /etc/apt/sources.list \
  && apt-get update
# Other sources:
# deb-src http://deb.debian.org/debian bookworm-updates main contrib non-free
# deb-src http://deb.debian.org/debian-security bookworm-security main contrib non-free

# Build dependencies for linux-pkvm / linux-pkvm-verif kernel
RUN apt build-dep -y linux

# Install dependencies
RUN apt-get update \
  && echo "Install general dependencies" \
  && apt-get install -y curl git \
  && echo "Install jsbsim proxy and libgpiod / vhost-device dependencies" \
  && apt-get install -y build-essential autoconf automake autoconf-archive \
  && echo "Install trusted boot dependencies" \
  && apt-get install -y  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  && echo "Install missing protection system (MPS) dependencies" \
  && apt-get install -y verilator python3-pip clang

# Install rustup & pin to 1.74
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o rustup.rs \
  && sh ./rustup.rs -y \
  && . "$HOME/.cargo/env"
ENV PATH="/root/.cargo/bin:$PATH"
RUN rustup toolchain install 1.74
RUN rustup default 1.74-x86_64-unknown-linux-gnu
RUN rustup target add aarch64-unknown-linux-gnu

# The following deps are needed to build the VM images
# Disk image and qemu dependencies
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
  qemu-system-arm qemu-utils \
  debian-installer-12-netboot-arm64 \
  cpio

WORKDIR /work
RUN rm -rf /tmp/*
