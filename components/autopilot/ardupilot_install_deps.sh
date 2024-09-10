#!/bin/bash
set -euo pipefail

# Script for installing ArduPilot build dependencies.

cd "$(dirname "$0")/ardupilot"

edo() {
    echo " >> $*" 1>&2
    "$@"
}

first() {
    echo "$1"
}

install_if_missing() {
    local package="$1"
    local file="$2"

    # If `$2` is a glob pattern, expand it to the first matching file if one
    # exists.
    if [[ ! -f "$(IFS='' first $file)" ]]; then
        echo "missing $file - need to install package $package" 1>&2
        edo sudo apt-get install -y "$package"
        if [[ ! -f "$(IFS='' first $file)" ]]; then
            echo "actual contents of $package:" 1>&2
            dpkg-query -L "$package" 1>&2
            echo "error: expected package $package to provide $file, but it did not" 1>&2
            return 1
        fi
    fi
}

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
