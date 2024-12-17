#!/bin/bash
set -euo pipefail
. "$(dirname "$0")/util.sh"

# Script for setting up `mavgen.py` and Ardupilot's `mavlink` submodule.  These
# are used to generate MAVLink protocol headers for other tools like the
# logging component.

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
    pip3 install pymavlink
)

# Initialize mavlink submodule
edo git submodule update --init modules/mavlink
