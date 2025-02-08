#!/usr/bin/env python3

# NOTE: If you make any change to this file, you must also update the measure
# in `test_config.ini` (otherwise the `test_attest` test case will fail).  The
# updated value can be computed with:
# 
# ../platform_crypto/shave_trusted_boot/calc_measure.py --measure-file test_attest_helper.py

import os
import sys

NONCE_SIZE = 16
MEASURE_SIZE = 32
HMAC_SIZE = 32

def read_exact(f, n):
    buf = bytearray(n)
    uninit = memoryview(buf)
    while len(uninit) > 0:
        amount = f.readinto(uninit)
        if amount == 0:
            return bytes(buf)[: len(buf) - len(uninit)]
        uninit = uninit[amount:]
    return bytes(buf)

def write_exact(f, b):
    remaining = memoryview(b)
    while len(remaining) > 0:
        amount = f.write(remaining)
        if amount == 0:
            raise OSError('unexpected EOF during write')
        remaining = remaining[amount:]

def main():
    fd = int(os.environ['VERSE_TRUSTED_BOOT_FD'])
    # Set `buffering=0` because `fdopen` requires the file descriptor to be
    # seekable unless buffering is disabled.
    sock = os.fdopen(fd, 'r+b', buffering=0)

    nonce = read_exact(sys.stdin.buffer, NONCE_SIZE)
    print('read nonce: %r' % (nonce,), file=sys.stderr)
    # Send "attest" command (2), followed by the nonce.
    write_exact(sock, b'\x02')
    write_exact(sock, nonce)
    print('wrote nonce', file=sys.stderr)
    attestation = read_exact(sock, MEASURE_SIZE + HMAC_SIZE)
    print('read attestation: %r' % (attestation,), file=sys.stderr)
    write_exact(sys.stdout.buffer, attestation)
    print('wrote attestation', file=sys.stderr)

if __name__ == '__main__':
    main()
