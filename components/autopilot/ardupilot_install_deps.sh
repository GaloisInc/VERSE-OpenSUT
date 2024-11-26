#!/bin/bash
set -euo pipefail
. "$(dirname "$0")/util.sh"

# Script for installing ArduPilot build dependencies.  Run with `BUILD_ONLY=1`
# to install only the dependencies required to build ArduPilot SITL binaries;
# the default is to install these and also dependencies of the mavproxy ground
# station software.

cd "$(dirname "$0")/ardupilot"

# Create Python virtualenv if it doesn't yet exist.
if [[ ! -d venv ]]; then
    edo install_if_missing python3-virtualenv /usr/bin/virtualenv
    virtualenv venv
fi

# Install Python dependencies into the virtualenv.  `pip install` is a no-op if
# the package is already installed.
(
    . venv/bin/activate
    pip3 install pexpect empy==3.3.4 future
    if [[ -z "${BUILD_ONLY:+x}" ]]; then
        pip3 install pymavlink MAVProxy opencv-python matplotlib

        # Extra system package needed for building wxPython
        edo install_if_missing libgtk-3-dev /usr/lib/*/pkgconfig/gtk+-3.0.pc
        # Note: the wxPython install builds from source, which takes a while
        pip3 install wxPython
    fi
)

install_if_missing gcc-aarch64-linux-gnu /usr/bin/aarch64-linux-gnu-gcc
install_if_missing g++-aarch64-linux-gnu /usr/bin/aarch64-linux-gnu-g++
