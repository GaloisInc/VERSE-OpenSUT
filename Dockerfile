# Top Level VERSE OpenSUT Dockerfile

# Labels added as described in
# https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#labelling-container-images
LABEL org.opencontainers.image.source=https://github.com/GaloisInc/VERSE-OpenSUT
LABEL org.opencontainers.image.description="VERSE-OpenSUT Base Platform Image"
LABEL org.opencontainers.image.licenses=BSD3

FROM --platform=linux/amd64 debian:bookworm

RUN apt-get clean \
    && apt-get update \
    && apt-get upgrade -y \
    && apt-get install -y vim

RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
  qemu-system-arm qemu-utils \
  debian-installer-12-netboot-arm64

# Prepare deb-src
RUN touch /etc/apt/sources.list \
    && echo "deb-src http://deb.debian.org/debian bookworm main contrib non-free" > /etc/apt/sources.list
# Other sources:
# deb-src http://deb.debian.org/debian bookworm-updates main contrib non-free
# deb-src http://deb.debian.org/debian-security bookworm-security main contrib non-free

# TODO: Add resources to the docker image
ADD src /opt/src
WORKDIR /opt

# Build the host and guest disk images.  This takes 1-2 hours.
RUN cd src/pkvm_setup \
    && bash create_disk_images.sh

# Build our patched version of QEMU in the host VM.  This takes 1-2 hours.
RUN cd src/pkvm_setup \
    && bash run_vm_script.sh vms/disk_host.img vm_scripts/install_qemu.sh
