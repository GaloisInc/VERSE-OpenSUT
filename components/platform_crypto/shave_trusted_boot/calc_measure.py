#!/usr/bin/env python3
'''
Compute a measure value, using the same algorithm as in `trusted_boot.c`.

Usage: `./calc_measure.py [STEPS...]`

The `STEPS` are performed in order.  Each step is one of:

* `--set 001122...`: Set the current measure to the provided hash.  This is
  useful if you've already computed a measure and now want to extend it.
* `--measure-file PATH`: Combine the contents of `PATH` with the current
  measure to compute a new measure.
* `--measure-hash-of-file PATH`: Combine the SHA256 hash of the contents of
  `PATH` with the current measure to compute a new measure.

Once all steps have been performed, the current measure is printed in
hexadecimal.
'''

import hashlib
import sys

MEASURE_SIZE = 32

MODES = {
        'set',
        'measure-file',
        'measure-hash-of-file',
        }

MODE_FLAGS = set('--' + x for x in MODES)

def parse_args():
    steps = []
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        i += 1

        if not arg.startswith('--'):
            raise ValueError('expected one of %r, but got %r'
                % (MODE_FLAGS, arg))
        arg = arg[2:]

        mode, eq, value = arg.partition('=')
        if mode not in MODES:
            raise ValueError('expected one of %r, but got %r'
                % (MODE_FLAGS, '--' + mode))

        if eq == '':
            # No equal sign in `arg`.  The value is the next argument.
            if i < len(sys.argv):
                value = sys.argv[i]
                i += 1
            else:
                raise ValueError('expected value after --%s' % arg)
        else:
            # The part after the equal sign is the value.
            pass

        steps.append((mode, value))

    return steps

def parse_hex(s):
    assert len(s) % 2 == 0, \
            'expected an even number of hex digits, but got %r (%d characters)' \
                % (s, len(s))
    b = bytes(int(s[i : i + 2], 16) for i in range(0, len(s), 2))
    return b

def main():
    steps = parse_args()

    # The initial measure is all zeros.
    current_measure = bytes(MEASURE_SIZE)

    for (mode, value) in steps:
        if mode == 'set':
            value_bytes = parse_hex(value)
            assert len(value_bytes) == MEASURE_SIZE, \
                    'expected %d bytes, but got %r (%d bytes)' \
                        % (MEASURE_SIZE, value, len(value_bytes))
            current_measure = value_bytes
        elif mode == 'measure-file':
            data = open(value, 'rb').read()
            sha256 = hashlib.sha256()
            sha256.update(data)
            sha256.update(current_measure)
            current_measure = sha256.digest()
        elif mode == 'measure-hash-of-file':
            data = open(value, 'rb').read()
            data_hash = hashlib.sha256(data).digest()
            sha256 = hashlib.sha256()
            sha256.update(data_hash)
            sha256.update(current_measure)
            current_measure = sha256.digest()
        else:
            assert False, 'impossible: no case for mode %r' % (mode,)

    print(''.join('%02x' % b for b in current_measure))
    print(', '.join('0x%02x' % b for b in current_measure))

if __name__ == '__main__':
    main()
