#!/bin/bash
set -euo pipefail

APP_DIR="$(cd "$(dirname "$0")" && pwd)"

# Provide a writable directory for `arduplane`.  It tries to write two things:
#  1. It saves the autopilot parameters to `./eeprom.bin`
#  2. It writes JSBSim config files to various places in the `autotest`
#     directory.  This directory path can be set with a command-line flag.
: "${RUN_DIR:=/var/run/ardupilot}"
mkdir -p "$RUN_DIR"
cd "$RUN_DIR"

# Remove old parameter storage so the autopilot always starts with the contents
# of the `--defaults` file rather than carrying over changes between runs.
rm -fv eeprom.bin

# Directories where `arduplane` will try to write JSBSim configs
mkdir -p autotest
mkdir -p autotest/aircraft/Rascal

# `--rate 250 --config 10` means that the autopilot runs at a 250 Hz update
# rate and the simulator runs at 10x that rate, or 2500 Hz.
"${APP_DIR}/arduplane" \
    --synthetic-clock --speedup 1 --slave 0 \
    --model jsbsim_ext \
    --defaults "$APP_DIR/plane-jsbsim-ext.parm" \
    --autotest-dir "$RUN_DIR/autotest" \
    --sim-address 10.0.2.2 --sim-port-out 5505 --sim-port-in 5504 \
    --rate 250 --config 10
echo "arduplane exited with code $?"
