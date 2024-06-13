# Top Level VERSE OpenSUT Dockerfile
FROM --platform=linux/amd64 debian:bookworm

# Labels added as described in
# https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#labelling-container-images
LABEL org.opencontainers.image.source=https://github.com/GaloisInc/VERSE-OpenSUT
LABEL org.opencontainers.image.description="VERSE-OpenSUT Base Platform Image"
LABEL org.opencontainers.image.licenses=BSD3

RUN apt-get clean \
    && apt-get update \
    && apt-get upgrade -y \
    && apt-get install -y vim

RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
  qemu-system-arm qemu-utils \
  debian-installer-12-netboot-arm64 \
  cpio

# Prepare deb-src
RUN touch /etc/apt/sources.list \
    && echo "deb-src http://deb.debian.org/debian bookworm main contrib non-free" > /etc/apt/sources.list
# Other sources:
# deb-src http://deb.debian.org/debian bookworm-updates main contrib non-free
# deb-src http://deb.debian.org/debian-security bookworm-security main contrib non-free

WORKDIR /opt
