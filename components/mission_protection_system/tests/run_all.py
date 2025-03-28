#!/usr/bin/env python3

#   Copyright 2021, 2022, 2023 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

# Top level driver for end-to-end testing
import subprocess
import glob
import os
import sys

# Turn off screen clearing ANSI
os.environ["MPS_NOCLEAR"] = "1"

# These tests should be run with the self-test binary,
# otherwise use the non self-test binary
NEEDS_SELF_TEST=[
    "scenarios/self_test",
    "scenarios/normal_14",
    "scenarios/exceptional_4a",
    "scenarios/exceptional_4b",
    "scenarios/exceptional_4c",
    "scenarios/exceptional_4d",
    "scenarios/exceptional_4e",
    ]

pass_count = 0
fail_count = 0
skip_count = 0
for test in sorted(glob.glob("scenarios/*")):
    fn, ext = os.path.splitext(test)
    if ext == ".cases":
        continue

    if not os.environ.get("MPS_SOCKET"):
        bin = "../src/mps.no_self_test"
        if fn in NEEDS_SELF_TEST:
            bin = "../src/mps.self_test"
        os.environ["MPS_BIN"] = bin
        os.environ.pop("MPS_SOCKET", None)
        print(f"{fn} ({bin})")
    else:
        if fn in NEEDS_SELF_TEST:
            # Most tests require an MPS binary built with SELF_TEST=Disabled,
            # but a few need SELF_TEST=Enabled instead.  Since we can't switch
            # binaries when testing through a socket, we run only the
            # SELF_TEST=Disabled part of the test suite.
            print('skipping test %r: requires SELF_TEST=Enabled' % fn)
            skip_count += 1
            continue
        # Remove MPS_BIN from the environment, if it's present.
        os.environ.pop("MPS_BIN", None)
        print(f"{fn} ({os.environ['MPS_SOCKET']})")

    try:
        if os.path.exists(fn + ".cases"):
            subprocess.run(["./test.py", fn, fn + ".cases"],check=True)
        else:
            subprocess.run(["./test.py", fn],check=True)
        pass_count += 1
    except subprocess.CalledProcessError:
        import traceback
        traceback.print_exc()
        fail_count += 1

print('\n%d tests passed, %d failed, %d skipped' % (pass_count, fail_count, skip_count))
if fail_count > 0:
    sys.exit(1)
