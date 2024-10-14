#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")/../.."

venv_dir=components/autopilot/ardupilot/venv/
mavproxy_bin="${venv_dir}/bin/mavproxy.py"

if [[ ! -d "$venv_dir" ]]; then
    echo "$venv_dir directory not found; create python virtual env and install deps first" 1>&2
    exit 1
fi

if [[ ! -f "$mavproxy_bin" ]]; then
    echo "$mavproxy_bin not found; install python deps first" 1>&2
    exit 1
fi

"$mavproxy_bin" --master tcp:127.0.0.1:5760 --map --console
