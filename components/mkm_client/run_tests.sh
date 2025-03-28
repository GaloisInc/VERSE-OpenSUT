#!/bin/bash
set -euo pipefail

(
    cd ../mission_key_management
    python3 convert_config.py test_config.ini test_config.bin
    ./mkm test_config.bin &
)
key=$(../platform_crypto/shave_trusted_boot/trusted_boot ./run_client.sh)
[ "$key" = "mkm_client uses this key to test" ]
