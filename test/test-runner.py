#!/usr/bin/env python3

import os
import sys
import logging
import subprocess
import argparse
import difflib

import toml

BASENAME = os.path.splitext(os.path.basename(__file__))[0]

logger = logging.getLogger(BASENAME)


def main():
    parser = argparse.ArgumentParser(BASENAME)
    parser.add_argument('--bin', help='A precompiled rockstarc binary to use')
    parser.add_argument('--rebuild',
                        help='Build and run the debug binary (if no binary is specified)',
                        action='store_true',
                        default=True)

    parser.add_argument('--refresh',
                        help='Overwrite output files with new results',
                        action='store_true')

    parser.add_argument('--tests-for-new-files',
                        help='Default tests to run for programs where no '
                             'configuration is present',
                        nargs='+',
                        metavar='test',
                        default=['tokens', 'pretty'])

    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument('files', nargs='*', help='Files to test')

    args = parser.parse_args()

    if args.verbose == 1:
        logger.setLevel(logging.INFO)
    elif args.verbose >= 2:
        logger.setLevel(logging.DEBUG)

    basedir = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

    if args.bin:
        binary = args.bin
    else:
        binary = os.path.join(basedir, 'target', 'debug', 'rstarc')

        if args.rebuild:
            logger.info('Invoking cargo build from %s', basedir)
            subprocess.check_call(['cargo', 'build'], cwd=basedir)

    files = args.files if args.files else get_files(basedir)

    if not verify_output(files,
                         binary=binary,
                         refresh=args.refresh,
                         tests_for_new_files=args.tests_for_new_files):
        sys.exit(1)


def get_files(basedir):
    files = []
    for (dirpath, _, filenames) in os.walk(os.path.join(basedir, 'test/programs')):
        for name in filenames:
            if name.endswith('.rock'):
                files.append(os.path.join(dirpath, name))
    return files


def verify_output(files, *, binary, refresh, tests_for_new_files):
    failures = []
    success_count = 0

    for src in files:
        outcomes = verify_source_file(src,
                                      binary=binary,
                                      refresh=refresh,
                                      tests_for_new_files=tests_for_new_files)

        for test, failed_reasons in sorted(outcomes.items()):

            if failed_reasons:
                failures.append((src, test, failed_reasons))
            else:
                success_count += 1

    for src, test, reasons in failures:
        print()
        print('FAILURE: {} for {}'.format(test, src))
        for reason in reasons:
            reason.explain()

    print('PASSED:', success_count)
    if refresh:
        print('UPDATED:', len(failures))
    else:
        print('FAILED:', len(failures))

    return not failures


def verify_source_file(src, binary, refresh, tests_for_new_files):
    logger.info('Verifying %s', src)

    actual_output = {}
    failures_by_test = {}

    config_filename = src + '.expected.toml'

    try:
        config = toml.load(config_filename)
        logger.debug('Using configuration file %s', config_filename)
    except FileNotFoundError:
        config = {
            'tests': {
                'enabled': tests_for_new_files,
            }
        }
        logger.debug('Configuration file %s missing', config_filename)

    tests = [
        ['tokens', [binary, 'internal', '--format=tokens', src]],
        ['pretty', [binary, 'internal', '--format=pretty', src]],
        ['run', [binary, 'run', src]],
    ]

    try:
        enabled_tests = config['tests']['enabled']
    except KeyError:
        raise ValueError('manifest for {} is missing enabled tests field'.format(src))

    for test, cmd in tests:
        if test not in enabled_tests:
            continue

        actual_output[test], failures_by_test[test] = \
            run_test(test_name=test, src=src, cmd=cmd, config=config)

    if refresh and any(failures for failures in failures_by_test.values()):
        logger.info('Updating %s', config_filename)

        for k, v in actual_output.items():
            config[k] = v

        with open(config_filename, 'w') as f:
            toml.dump(config, f)

    return failures_by_test


def run_test(test_name, src, cmd, config):
    logger.debug('Testing %s with command %s', test_name, cmd)

    proc = subprocess.Popen(cmd,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            universal_newlines=True)

    proc.wait()
    out, err = proc.communicate()

    output = {
        'returncode': str(proc.returncode),
    }

    if out: output['stdout'] = out
    if err: output['stderr'] = err

    failures = validate_output(test_name, config, output)

    return output, failures


def validate_output(test_name, config, output):
    failures = []

    if not test_name in config:
        failures.append(UnexpectedOutput(output))
    else:
        for field in ['returncode', 'stdout', 'stderr']:
            validate_field(failures, field, config[test_name], output)

    return failures


def validate_field(failures, field, test_config, output):
    if field not in output and field not in test_config:
        return

    if field in output and field not in test_config:
        failures.append(UnexpectedOutput({
            field: output[field]
        }))

    elif field in test_config and field not in output:
        failures.append(NonMatching(field=field,
                                    actual='',
                                    expected=test_config[field]))

    elif output[field] != test_config[field]:
        failures.append(NonMatching(field=field,
                                    actual=output[field],
                                    expected=test_config[field]))


class UnexpectedOutput:
    def __init__(self, fields):
        self.fields = fields

    def explain(self):
        for k, v in sorted(self.fields.items()):
            print('Unexpected output for field {!r}:'.format(k))
            for line in v.splitlines():
                if not line:
                    print()
                else:
                    print(' ' + line)
            print()


class NonMatching:
    def __init__(self, field, actual, expected):
        self.field = field
        self.actual = actual
        self.expected = expected

    def explain(self):
        print('Unexpected value for field {!r}:'.format(self.field))
        differ = difflib.Differ()

        diff = differ.compare(self.expected.splitlines(keepends=True),
                              self.actual.splitlines(keepends=True))

        for line in diff:
            print(line, end='' if line.endswith('\n') else '\n')


if __name__ == '__main__':
    logging.basicConfig()
    main()
