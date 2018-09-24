#!/usr/bin/env python3

import os
import sys
import argparse
import subprocess


def main():
    parser = argparse.ArgumentParser(description='Wrapper to build the '
                                                 'runtime with a Rust nightly '
                                                 'invoked via rustup.')

    parser.add_argument('extra_args',
                        nargs=argparse.REMAINDER,
                        help='Arguments to pass to "cargo build"')

    args = parser.parse_args()

    basedir = os.path.dirname(os.path.realpath(__file__))
    cmd = ['rustup', 'run', 'nightly', 'cargo'] + args.extra_args
    subprocess.check_call(cmd, cwd=os.path.join(basedir, 'runtime/roll'))


if __name__ == '__main__':
    main()
