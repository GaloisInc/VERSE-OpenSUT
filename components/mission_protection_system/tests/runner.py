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

# Run a test on a single input

import pexpect
import pexpect.fdpexpect
import sys
import os
import socket
import struct
import threading
import time


MPS_BIN = os.environ.get("MPS_BIN")
MPS_SOCKET = os.environ.get("MPS_SOCKET")
MPS_DEBUG = os.environ.get("MPS_DEBUG") is not None

MPS_GPIO_SOCKET = os.environ.get("MPS_GPIO_SOCKET")

class GPIOState:
    def __init__(self):
        self.state = [-1, -1]
        self.cv = threading.Condition()

    def set(self, i, val):
        with self.cv:
            self.state[i] = val
            self.cv.notify_all()

    def wait(self, expect_state, timeout = None):
        """
        Wait until `self.state == expect_state`.
        """
        with self.cv:
            ok = self.cv.wait_for(lambda: self.state == expect_state, timeout = timeout)
            if not ok:
                raise TimeoutError()

GPIO_STATE = GPIOState()

def gpio_thread(sock):
    buf = b''
    while True:
        b = sock.recv(2 - len(buf))
        if len(b) != 2:
            if len(b) == 0:
                break
            elif len(buf) + len(b) == 2:
                b = buf + b
                buf = b''
            else:
                buf = buf + b
                continue
        assert len(b) == 2

        i, val = struct.unpack('Bb', b)
        GPIO_STATE.set(i, val)

def start_gpio_thread(socket_path):
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.connect(socket_path)
    thread = threading.Thread(target = gpio_thread, args = (sock,),
        daemon = True)
    thread.start()

def string_to_hw_actuators_state(s):
    if b'HW ACTUATORS ' not in s:
        return None

    _, _, rest = s.partition(b'HW ACTUATORS ')
    parts = rest.strip().split()
    if len(parts) < 2:
        return None
    state = []
    for part in parts[:2]:
        if part == b'ON':
            state.append(1)
        elif part == b'OFF':
            state.append(0)
        else:
            return None
    return state

def try_expect(p,expected,timeout=60,retries=10):
    expected = expected.strip()
    if MPS_DEBUG:
        print(f"CHECKING: {expected}")
    while retries > 0:
        p.sendline('D')
        try:
            p.expect(expected.strip() + "\r\n", timeout)
        except pexpect.TIMEOUT:
            retries = retries - 1
            if MPS_DEBUG:
                print(f"...{retries} retries remaining",end='\r')
            continue
        if MPS_DEBUG:
            print(f"CHECKING: {expected} succeeded")

        if (state := string_to_hw_actuators_state(p.match.group())) is not None:
            # Wait for GPIO values to match the requested state
            if MPS_DEBUG:
                print(f"GPIO: checking for state %r" % (state,))
            try:
                GPIO_STATE.wait(state, timeout = 10)
            except TimeoutError:
                print(f"GPIO: check for state %r failed" % (state,))
                return False
            if MPS_DEBUG:
                print(f"GPIO: check succeeded")

        return True
    if MPS_DEBUG:
        print(f"CHECKING: {expected} failed")
    return False

def run_script(p, cmds):
    in_block = False
    block = ''
    for i,c in enumerate(cmds):
        if len(c) == 0:
            continue

        if c.strip() == '???':
            if in_block:
                in_block = False
                if try_expect(p, block):
                    block = ''
                    continue
                else:
                    return False
            else:
                in_block = True
            continue

        if in_block:
            if block != '':
                block += "\\r\\n"
            block += c.strip()

        elif c[0] == '?':
            if try_expect(p,c[1:]):
                continue
            else:
                return False
        else:
            if MPS_DEBUG:
                print(f"SENDING: {c.strip()}")
            p.sendline(c.strip())
            p.sendline('')
        time.sleep(0.1)
    return True

def run(script, args):
    if not MPS_SOCKET:
        p = pexpect.spawn(MPS_BIN)
    else:
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.connect(MPS_SOCKET)
        p = pexpect.fdpexpect.fdspawn(sock.fileno())
        # Reset the MPS to its initial state.
        p.sendline('R')
        try_expect(p, 'RESET')
    time.sleep(0.1)

    if MPS_GPIO_SOCKET:
        start_gpio_thread(MPS_GPIO_SOCKET)

    with open(script) as f:
        cmds = f.readlines()
        fst = cmds[0].strip()
        params = {}
        if fst[0] == '{' and fst[-1] == '}':
            pnames = [x.strip() for x in fst[1:-1].split(',')]
            if len(args) != len(pnames):
                return False
            for (var, val) in zip(pnames, args):
                params[var] = val
            cmds = cmds[1:]

        formatted = [cmd.format(**params) for cmd in cmds]

        return run_script(p, formatted)

def main():
    script = sys.argv[1]
    args = sys.argv[2:] if len(sys.argv) > 2 else []

    if MPS_BIN is None:
        print("Error: MPS_BIN should be set to mps binary to test")
        sys.exit(1)

    if run(script, args):
        print("PASS")
        sys.exit(0)
    else:
        print("FAIL")
        sys.exit(1)

if __name__ == "__main__":
    main()
