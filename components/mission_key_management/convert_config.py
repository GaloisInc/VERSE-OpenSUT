'''
Convert an MKM policy configuration from text to binary format.  The text
format is INI (as handled by Python's `configparser` module) with sections like
this:

    [00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff]
    key0 = aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
    key255 = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb

This means that if the component with measure `001122...` requests key ID 0, it
should be sent key `aaaa...`, and if it requests key ID 255, it should be sent
`bbbb...`.
'''
import argparse
import configparser
import struct

MEASURE_SIZE = 32
KEY_ID_SIZE = 1
KEY_ID_FMT = '<B'
KEY_SIZE = 32

assert struct.calcsize(KEY_ID_FMT) == KEY_ID_SIZE

def parse_args():
    ap = argparse.ArgumentParser()
    ap.add_argument('ini_path',
        help='path to the input file in text/INI format')
    ap.add_argument('bin_path',
        help='path to the output file in binary format')
    return ap.parse_args()

def parse_hex(s):
    assert len(s) % 2 == 0, \
            'expected an even number of hex digits, but got %r (%d characters)' \
                % (s, len(s))
    b = bytes(int(s[i : i + 2], 16) for i in range(0, len(s), 2))
    return b

def main():
    args = parse_args()

    cfg = configparser.ConfigParser()
    cfg.read_file(open(args.ini_path))

    f = open(args.bin_path, 'wb')

    for measure_str, keys in cfg.items():
        if measure_str == 'DEFAULT' and len(keys) == 0:
            continue

        measure = parse_hex(measure_str)
        assert len(measure) == MEASURE_SIZE, \
                'expected measure to be %d bytes, but got %r (%d bytes)' \
                    % (MEASURE_SIZE, measure_str, len(measure))
        
        for key_id_str, key_str in keys.items():
            assert key_id_str.startswith('key'), \
                    'expected `key` followed by a number, but got %r' % (key_id_str,)
            key_id = int(key_id_str[len('key'):])
            key_id_bytes = struct.pack(KEY_ID_FMT, key_id)
            key = parse_hex(key_str)

            f.write(measure + key_id_bytes + key)


if __name__ == '__main__':
    main()
