'''
Script for building an application image for use with `opensut_boot`.  This is
a wrapper around `mksquashfs` that makes it easier to gather files from
multiple places into a single image.
'''

import argparse
import os
import shutil
import subprocess
import tempfile

def parse_args():
    parser = argparse.ArgumentParser(
        description = 'build an opensut_boot application image')
    parser.add_argument('--file', '-f', action='append', metavar='SRC[=DEST]', default=[],
        help = 'include file SRC at path DEST (default: basename(SRC)) '
            'in the generated image')
    parser.add_argument('--dir', '-d', action='append', metavar='SRC[=DEST]', default=[],
        help = 'include directory SRC at path DEST (default: basename(SRC)) '
            'in the generated image')
    parser.add_argument('--output', '-o', metavar='OUT.IMG', default='out.img',
        help = 'where to write the generated image')

    return parser.parse_args()

def main():
    args = parse_args()

    temp_dir = tempfile.TemporaryDirectory()

    for file_spec in args.file:
        src, delim, dest = file_spec.partition('=')
        if delim == '':
            assert dest == ''
            dest = os.path.basename(src)
        assert not os.path.isabs(dest), 'destination path must be relative (got %r)' % dest
        dest_full = os.path.join(temp_dir.name, dest)
        os.makedirs(os.path.dirname(dest_full), exist_ok=True)
        shutil.copyfile(src, dest_full)
        shutil.copystat(src, dest_full)

    for dir_spec in args.dir:
        src, delim, dest = dir_spec.partition('=')
        if delim == '':
            assert dest == ''
            dest = os.path.basename(src)
        assert not os.path.isabs(dest), 'destination path must be relative (got %r)' % dest
        dest_full = os.path.join(temp_dir.name, dest)
        os.makedirs(os.path.dirname(dest_full), exist_ok=True)
        shutil.copytree(src, dest_full)

    subprocess.run(('mksquashfs', temp_dir.name, args.output, '-noappend'),
        check = True)

if __name__ == '__main__':
    main()
