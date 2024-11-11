#!/bin/bash
set -euo pipefail
. "$(dirname "$0")/util.sh"

# Initialize ArduPilot submodules that are needed for the SITL build.

cd "$(dirname "$0")/ardupilot"

modules=(
    waf
    DroneCAN/dronecan_dsdlc
    DroneCAN/pydronecan
    DroneCAN/DSDL
    DroneCAN/libcanard
)

for x in "${modules[@]}"; do
    edo git submodule update --init "modules/$x"
done
