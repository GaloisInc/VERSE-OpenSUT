#!/bin/bash
set -euo pipefail

apt install -y python3-pexpect

echo "Starting test suite"
cd tests
MPS_DEBUG=1 python3 run_all.py
