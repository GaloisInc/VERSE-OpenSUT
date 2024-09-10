#!/bin/bash
set -euo pipefail

# Initialize ArduPilot submodules that are needed for the SITL build.

cd "$(dirname "$0")/ardupilot"

edo() {
    echo " >> $*" 1>&2
    "$@"
}

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
