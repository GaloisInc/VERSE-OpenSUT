#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")/../.."

jsbsim_bin=components/autopilot/jsbsim/build/src/JSBSim
jsbsim_proxy_bin=src/jsbsim_proxy/jsbsim_proxy
xml_dir=components/autopilot/jsbsim_config

if [[ ! -f "$jsbsim_proxy_bin" ]]; then
    echo "$jsbsim_proxy_bin not found; build jsbsim_proxy first" 1>&2
    exit 1
fi

if [[ ! -f "$jsbsim_bin" ]]; then
    echo "$jsbsim_bin not found; build JSBSim first" 1>&2
    exit 1
fi

# We pass `--root=$xml_dir` so that JSBSim can find the scripts and aircraft
# definition files.
"$jsbsim_proxy_bin" "$jsbsim_bin" \
    --suspend \
    --simulation-rate=2500 \
    --root="$xml_dir" \
    --logdirectivefile="jsbsim_fgout_vm.xml" \
    --script="jsbsim_start_vm.xml" \
    --nice=0.00000001
