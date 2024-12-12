#!/usr/bin/env python3
'''
Compute a measure value, using the same algorithm as in `trusted_boot.c`.

Usage: `./calc_measure.py [FILES...]`

This starts with an initial measure, then hashes the contents of each of the
`FILES` into the measure, and finally prints the result in hexadecimal.
'''

import hashlib
import sys

MEASURE_SIZE = 32

def main():
    current_measure = bytes(MEASURE_SIZE)

    for filename in sys.argv[1:]:
        data = open(filename, 'rb').read()
        sha256 = hashlib.sha256()
        sha256.update(data)
        sha256.update(current_measure)
        current_measure = sha256.digest()

    print(''.join('%02x' % b for b in current_measure))
    print(', '.join('0x%02x' % b for b in current_measure))



if __name__ == '__main__':
    main()
