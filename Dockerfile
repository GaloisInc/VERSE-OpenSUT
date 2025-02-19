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

# mps-build
RUN apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  && apt-get install -y verilator

# trusted-boot-build
RUN apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# mps-test
RUN apt-get install -y python3-pip

# trusted-boot-build
RUN apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# vm_runner
RUN apt-get install -y gcc-aarch64-linux-gnu
# Plus Rust 1.74 toolchain, installed below

# libgpiod
RUN apt-get install -y \
  build-essential autoconf automake autoconf-archive \
  gcc-aarch64-linux-gnu

# vhost_device
RUN apt-get install -y \
  build-essential autoconf automake autoconf-archive \
  gcc-aarch64-linux-gnu
# Plus Rust 1.74 toolchain, installed below

# pkvm
# (no dependencies)

# qemu
# (no dependencies)

# vm_image_base
# (no dependencies)

# vm_images
RUN apt-get install -y qemu-system-arm qemu-utils

# mps-test-vm
RUN apt-get install -y qemu-system-arm

# ardupilot
# The deps are handled by the install scripts below

# logging
RUN apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# jsbsim_proxy
RUN apt-get install -y build-essential

# mkm
RUN apt-get install -y build-essential \
  && apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# mkm_client
RUN apt-get install -y build-essential \
  && apt-get install -y gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# jsbsim
RUN apt-get install -y build-essential cmake


# Install rustup & pin to 1.74
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o rustup.rs \
  && sh ./rustup.rs -y --default-toolchain 1.74
ENV PATH="/root/.cargo/bin:$PATH"
RUN rustup target add aarch64-unknown-linux-gnu


# Dependencies required to run vm_runner
RUN apt-get install -y squashfs-tools
RUN apt-get install -y qemu-system-arm


COPY . /opt/OpenSUT
WORKDIR /opt/OpenSUT


# FIXME: when running `docker build` locally, there may be extra package
# versions in the `packages` directory, which will overwrite each other
# arbitrarily here
RUN for f in packages/*; do tar -xvf "$f"; done
RUN rm -v packages/*


# Build components that aren't managed by package.sh

# jsbsim_proxy
WORKDIR /opt/OpenSUT/src/jsbsim_proxy
RUN make

# mkm
WORKDIR /opt/OpenSUT/components/mission_key_management
RUN make
RUN make TARGET=aarch64

# mkm_client
WORKDIR /opt/OpenSUT/components/mkm_client
RUN make
RUN make TARGET=aarch64

# JSBSim
WORKDIR /opt/OpenSUT/components/autopilot
RUN bash jsbsim_build.sh
