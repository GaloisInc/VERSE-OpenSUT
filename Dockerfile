# syntax=docker/dockerfile:1.7-labs

# Top Level VERSE OpenSUT Dockerfile
# NOTE: migrating to a newer OS to support MPS test job
FROM --platform=linux/amd64 ubuntu:24.04

# Labels added as described in
# https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#labelling-container-images
LABEL org.opencontainers.image.source=https://github.com/GaloisInc/VERSE-OpenSUT
LABEL org.opencontainers.image.description="VERSE-OpenSUT Base Platform Image"
LABEL org.opencontainers.image.licenses=BSD3

# Upgrade to the latest version of all packages
RUN apt-get clean \
  && apt-get update \
  && apt-get upgrade -y \
  && apt-get install -y curl git

# Install system packages for all stages
# This step is *before* we add the OpenSUT repo
# to maximize caching
#
# MPS
RUN apt-get update \
  && apt-get install -y verilator \
  && apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  && apt-get install -y python3-pip

# Trusted boot
# (identical to the previous stage)
#RUN apt-get update \
#  && apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# VM Runner
# (identical to the previous stage)
#RUN apt-get update \
#  && apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu
# Install rustup & pin to 1.74
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o rustup.rs \
  && sh ./rustup.rs -y \
  && . "$HOME/.cargo/env"
ENV PATH="/root/.cargo/bin:$PATH"
RUN rustup toolchain install 1.74
RUN rustup default 1.74-x86_64-unknown-linux-gnu
RUN rustup target add aarch64-unknown-linux-gnu
ENV RUSTUP_TOOLCHAIN=1.74

## DEPENDENCY INSTALL ##
# libgpiod
RUN apt-get update \
  && apt-get install -y \
  build-essential autoconf automake autoconf-archive \
  gcc-aarch64-linux-gnu

# vhost_device
# (identical to the previous stage)
# RUN apt-get update \
#   && apt-get install -y \
#   build-essential autoconf automake autoconf-archive \

# pkvm
# (will be downloaded from artifactory)

# qemu
# (will be downloaded from artifactory)

# vm_image_base
# (will be downloaded from artifactory)

# vm_images
RUN apt-get update \
  && apt-get install -y qemu-system-arm qemu-utils

# mps-test-vm
RUN apt-get update \
  && apt-get install -y qemu-system-arm

# ardupilot
# The deps are handled by the install scripts below

# jsbsim_proxy
# (identical to the previous stage)
# RUN apt-get update \
#   && apt-get install -y build-essential
## DEPENDENCY INSTALL ##

COPY . /opt/OpenSUT
WORKDIR /opt/OpenSUT

## BUILD ##

# ardupilot


# jsbsim_proxy
RUN cd src/jsbsim_proxy \
  && make \
  && [ -f jsbsim_proxy ]
## BUILD ##

# # ardupilot
# RUN git submodule update --init components/autopilot/ardupilot

# # Install dependencies
# RUN apt-get update \
#   && echo "Install general dependencies" \
#   && apt-get install -y curl git pkg-config m4 \
#   && echo "Install jsbsim proxy and libgpiod / vhost-device dependencies" \
#   && apt-get install -y build-essential autoconf automake autoconf-archive libtool \
#   && echo "Install trusted boot dependencies" \
#   && apt-get install -y  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
#   && echo "Install missing protection system (MPS) dependencies" \
#   && apt-get install -y verilator python3-pip clang



# # Prepare deb-src
# RUN touch /etc/apt/sources.list \
#   && echo "deb-src http://deb.debian.org/debian bookworm main contrib non-free" > /etc/apt/sources.list \
#   && apt-get update
# # Other sources:
# # deb-src http://deb.debian.org/debian bookworm-updates main contrib non-free
# # deb-src http://deb.debian.org/debian-security bookworm-security main contrib non-free

# # Build dependencies for linux-pkvm / linux-pkvm-verif kernel
# RUN apt build-dep -y linux

# # The following deps are needed to build the VM images
# # Disk image and qemu dependencies
# # bash src/pkvm_setup/package.sh full_build {qemu,pkvm,vm_image_base}
# RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
#   qemu-system-arm qemu-utils \
#   debian-installer-12-netboot-arm64 \
#   cpio

WORKDIR /work
RUN rm -rf /tmp/*
