#!/bin/bash
set -euo pipefail
# Setup script to be run inside the common VM image with `run_vm_script.sh`.

echo "setup_common.sh ($0) running"

edo() {
    echo " >> $*"
    "$@"
}

# Enable passwordless sudo for `user`
edo tee -a /etc/sudoers <<EOF
user ALL=(ALL) NOPASSWD: ALL
EOF


edo apt clean
edo fstrim -v /
