#!/usr/bin/env python3

import re
import os
import sys
import time
import asyncio
import logging
import subprocess
import argparse
import difflib
from contextlib import closing

import rtoml as toml

BASENAME = os.path.splitext(os.path.basename(__file__))[0]

logger = logging.getLogger(BASENAME)


def main():
    parser = argparse.ArgumentParser(BASENAME)
    parser.add_argument('--bin', help='Use a prebuilt compiler binary')
    parser.add_argument('--no-rebuild',
                        help='Skip rebuilding the compiler and runtime',
                        action='store_false',
                        dest='rebuild',
                        default=True)

    parser.add_argument('--refresh',
                        help='Overwrite output files with new results',
                        default=False,
                        const=True,
                        choices=['force'],
                        nargs='?')

    parser.add_argument('--tests-for-new-files',
                        help='Default tests to run for programs where no '
                             'configuration is present',
                        nargs='+',
                        metavar='test',
                        default=['tokens', 'pretty'])

    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument('sources', nargs='*', help='Files and directories to test')

    args = parser.parse_args()

    if args.verbose == 1:
        logger.setLevel(logging.INFO)
    elif args.verbose >= 2:
        logger.setLevel(logging.DEBUG)

    basedir = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

    if args.bin:
        binary = args.bin
    else:
        binary = cwd_relative(os.path.join(basedir, 'target', 'debug', 'rstarc'))

        if args.rebuild:
            cmd = ['cargo', 'build']
            logger.info('Invoking %s from %s', cmd, basedir)
            subprocess.check_call(cmd, cwd=basedir)

    if args.rebuild:
        cmd = ['cargo', 'build', '--release']
        runtime_dir = os.path.join(basedir, 'runtime', 'roll')
        logger.info('Invoking %s from %s', cmd, runtime_dir)
        subprocess.check_call(cmd, cwd=runtime_dir)

    if args.sources:
        sources = args.sources
    else:
        sources = [os.path.join(basedir, 'test/programs')]

    files = get_files(sources)
    logger.debug('Targeting files %s', files)

    if not verify_output(files,
                         binary=binary,
                         refresh=args.refresh,
                         tests_for_new_files=args.tests_for_new_files):
        sys.exit(1)


def get_files(locations):
    files = []

    logger.debug('Searching locations %s', locations)

    for loc in locations:
        if os.path.isdir(loc):
            files.extend(get_files_in_dir(loc))
        else:
            files.append(loc)

    return [cwd_relative(f) for f in files]


def get_files_in_dir(dir):
    files = []

    for (dirpath, _, filenames) in os.walk(dir):
        for name in filenames:
            if name.endswith('.rock'):
                files.append(os.path.join(dirpath, name))
    return files


def cwd_relative(path):
    cwd = os.path.realpath(os.getcwd())
    if not cwd.endswith(os.path.sep):
        cwd += os.path.sep

    path = os.path.realpath(path)

    if path.startswith(cwd):
        return path[len(cwd):]

    return path


def verify_output(files, *, binary, refresh, tests_for_new_files):
    with closing(asyncio.get_event_loop()) as loop:
        results = loop.run_until_complete(
            run_tests_parallel(files,
                               binary=binary,
                               refresh=refresh,
                               tests_for_new_files=tests_for_new_files)
        )

    failures = []
    success_count = 0

    for result in results:
        for test, failed_reasons in result.failed_tests():
            failures.append((result.input_program, test, failed_reasons))

        success_count += len(result.successful_tests())

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


async def run_tests_parallel(files, *, binary, refresh, tests_for_new_files):
    tasks = [
        asyncio.ensure_future(
            verify_source_file(src,
                               binary=binary,
                               refresh=refresh,
                               tests_for_new_files=tests_for_new_files)
        )
        for src in files
    ]

    results = []

    for task in asyncio.as_completed(tasks):
        try:
            result = await task
        except asyncio.CancelledError:
            pass
        except Exception:
            for task in tasks:
                if task.done():
                    continue

                task.cancel()

            # TODO: should log additional exceptions from other tasks?
            for task in tasks:
                if task.done():
                    continue

                try:
                    await task
                except asyncio.CancelledError:
                    pass
                except Exception:
                    logger.exception('Error on task cleanup')

            raise

        results.append(result)

    return results


async def verify_source_file(src, *, binary, refresh, tests_for_new_files):
    logger.info('Verifying %s', src)

    config_filename = src + '.expected.toml'

    try:
        with open(config_filename) as f:
            config = toml.load(f)

        logger.debug('Using configuration file %s', config_filename)
    except FileNotFoundError:
        config = {
            'tests': {
                'enabled': tests_for_new_files,
            }
        }
        logger.debug('Configuration file %s missing', config_filename)

    try:
        enabled_tests = config['tests']['enabled']
    except KeyError:
        raise ValueError('manifest for {} is missing enabled tests field'.format(src))

    test_results = TestResults(src)

    for test in TestRegistry.expand_tests(enabled_tests):
        cmd = TestRegistry.command_for_test(test, binary=binary, src=src)

        output, failures = await run_test(test_name=test, src=src, cmd=cmd, config=config)
        test_results.register_result(test=test, output=output, failures=failures)

    if needs_refresh(refresh, test_results):
        logger.info('Updating %s', config_filename)

        config = {
            'tests': config['tests'],
        }

        for k, v in test_results.contract_output():
            config[k] = v

        write_toml(config, config_filename)

    return test_results


def needs_refresh(refresh, test_results):
    if not refresh:
        return False

    if refresh == 'force':
        return True

    return bool(test_results.failed_tests())


class TestRegistry:
    _registered = {
        'tokens': lambda src: ['internal', '--debug-print=tokens', src],
        'pretty.fromsource': lambda src: ['internal', '--debug-print=pretty', src],
        'pretty.iterated': lambda src: ['internal', '--debug-print=pretty-iterated', src],
        'ast': lambda src: ['internal', '--debug-print=ast', src],
        'ir': lambda src: ['internal', '--debug-print=ir', src],
        'run.exec': lambda src: ['run', src],
        'run.interpret': lambda src: ['run', '--interpret', src],
    }

    @classmethod
    def command_for_test(cls, test, *, binary, src):
        try:
            registered = cls._registered[test]
        except KeyError:
            raise ValueError(f'Unknown test {test} configured for {src}')

        return [binary] + registered(src=src)

    @classmethod
    def expand_tests(cls, enabled_tests):
        expanded = []

        for test_name in enabled_tests:
            for full_name in cls._registered:
                if (full_name == test_name or
                        full_name.startswith(test_name + '.')):

                    if full_name not in expanded:
                        expanded.append(full_name)

        return expanded

    @classmethod
    def prefixes_by_precedence(cls):
        """
        Return prefixes in an order such that more-specific prefixes follow
        their less-specific counterparts. The ordering is otherwise
        unspecified.
        """
        all_prefixes = {}

        for test in cls._registered:
            parts = test.split('.')
            for i in range(len(parts) - 1):
                prefix = '.'.join(parts[:i + 1])
                all_prefixes.setdefault(prefix, []).append(test)

        return sorted(all_prefixes.items(), key=lambda item: len(item[0]))


class TestResults:
    def __init__(self, input_program):
        self.input_program = input_program
        self.actual_output = {}
        self.failures_by_test = {}

    def register_result(self, test, output, failures):
        assert test not in self.actual_output
        assert test not in self.failures_by_test
        self.actual_output[test] = output
        self.failures_by_test[test] = failures

    def failed_tests(self):
        return sorted((k, v) for k, v in self.failures_by_test.items() if v)

    def successful_tests(self):
        return sorted(k for k, v in self.failures_by_test.items() if not v)

    def contract_output(self):
        contracted = {}

        tests_covered = set()
        prefixes_tested = set()

        prefixes = TestRegistry.prefixes_by_precedence()

        # Do dict construction in a single pass so that output ordering
        # matches the ordering of results
        #
        # FIXME: Is that really an invariant worth maintaining?

        for test, result in self.actual_output.items():
            if test in tests_covered:
                continue

            for prefix, subtests in prefixes:
                if prefix in prefixes_tested or test not in subtests:
                    continue

                prefixes_tested.add(prefix)
                summary_result = self._aggregate_results(subtests)

                if summary_result is not None:
                    tests_covered.update(subtests)
                    contracted[prefix] = summary_result
                    break

            else:
                tests_covered.add(test)
                contracted[test] = result

        return list(contracted.items())

    def _aggregate_results(self, tests):
        aggregate = None

        for test in tests:
            if test not in self.actual_output:
                return None

            if aggregate is None:
                aggregate = self.actual_output[test]

            elif self.actual_output[test] != aggregate:
                return None

        return aggregate


async def run_test(test_name, src, cmd, config):
    logger.debug('Testing %s with command %s', test_name, cmd)

    start = time.time()

    proc = await asyncio.create_subprocess_exec(*cmd,
                                                stdout=subprocess.PIPE,
                                                stderr=subprocess.PIPE)

    try:
        await proc.wait()
        out, err = await proc.communicate()

    except:
        proc.kill()
        raise

    end = time.time()

    logger.debug('Elapsed for %s %s: %.2fs', src, test_name, end - start)

    out = out.decode('utf-8')
    err = err.decode('utf-8')

    output = {
        'returncode': str(proc.returncode),
    }

    if out: output['stdout'] = out
    if err: output['stderr'] = err

    failures = validate_output(test_name, config, output)

    return output, failures


def validate_output(test_name, config, output):
    failures = []

    expected = get_expected_output(test_name, config)

    if expected is None:
        failures.append(UnexpectedOutput(output))
    else:
        for field in ['returncode', 'stdout', 'stderr']:
            validate_field(failures, field, expected, output)

    return failures


def get_expected_output(test_name, config):
    parts = test_name.split('.')
    for i in reversed(range(1, len(parts) + 1)):
        prefix = '.'.join(parts[:i])
        if prefix in config:
            return config[prefix]
    return None


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


def write_toml(source_object, fname):
    """
    Find pairs of bare keys and single-line basic strings and replace them
    with multi-line basic strings.
    """
    content = toml.dumps(source_object)

    with open(fname, 'w') as f:
        end_idx = 0

        for match in re.finditer(r'^([A-Za-z0-9_-]+)\s*=\s*"(.*)"$', content, re.MULTILINE):
            key = match.group(1)
            string = match.group(2)

            if '\\n' not in string:
                continue

            f.write(content[end_idx:match.start()])

            multiline = expand_toml_string(key, string)
            f.write(f'{key} = """\n{multiline}"""')

            end_idx = match.end()

        f.write(content[end_idx:])


def expand_toml_string(key: str, string: str) -> str:
    """hack: rewrite string literals into multiline form

    The rtoml library outputs single-line literals, but we want multiline
    string literals for readability.
    """
    chars = iter(string)

    multiline = []

    while True:
        next_char = next(chars, None)

        if next_char is None:
            break

        if next_char != '\\':
            multiline.append(next_char)
            continue

        escaped = next(chars, None)
        if escaped is None:
            raise RuntimeError(f'unexpected EOF when modifying TOML key {key}')

        if escaped == 'n':
            multiline.append('\n')
        elif escaped == '"':
            multiline.append('"')
        else:
            multiline.extend(['\\', escaped])

    # Still need to escape three consecutive `"`s
    return ''.join(multiline).replace('"""', '\\"\\"\\"')


if __name__ == '__main__':
    logging.basicConfig()
    main()
