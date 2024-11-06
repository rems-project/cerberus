#!/usr/bin/env python3

import os, sys, re, subprocess, json, difflib, argparse, concurrent.futures

test_matcher = re.compile(r'^(.*\.c?)$')

def eprint(*args, then_exit=True, **kwargs):
    print('Error:', *args, file=sys.stderr, **kwargs)
    if then_exit:
        exit(1)

def test_files(test_dir):
    if not os.path.isdir(test_dir):
        eprint(f"'{test_dir}' not a directory")
    for root, _, files in os.walk(test_dir):
        for filename in files:
            if test_matcher.match(filename) is not None:
                yield os.path.join(root, filename)

class CN:

    def __init__(self, cn, timeout):
        self.cn = cn
        self.timeout = timeout

    def run(self, test_rel_path):
        return subprocess.run([self.cn, 'verify', test_rel_path], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=self.timeout)

    def output(self, test_rel_path):
        try:
            completed = self.run(test_rel_path);
            result = ("return code: %d\n%s" % (completed.returncode, completed.stdout))
        except subprocess.TimeoutExpired:
            result = "TIMEOUT\n"
        return result.splitlines(True)

    def get_diff(self, test_rel_path):
        expect_path = test_rel_path + '.expected'
        if not os.path.isfile(expect_path):
            open(expect_path, 'w')
        with open(expect_path, 'r') as expect:
            return list(difflib.unified_diff(expect.readlines(), self.output(test_rel_path), expect_path, expect_path))


def filter_tests(test_dir, suffix):
    inputs = test_files(test_dir)
    if suffix is not None:
        inputs = list(filter(lambda x : x.endswith(suffix), inputs))
        inputs_len = len(inputs)
        if inputs_len > 1:
            eprint(f'more than one file matching *{suffix} found in {test_dir}', then_exit=False)
            eprint(inputs)
        elif inputs_len == 0:
            eprint(f'*{suffix} not found in {test_dir}')
    return inputs


def run_tests(args):
    failed_tests = 0
    cn = CN(args.cn, args.timeout)
    test_rel_paths = list(filter_tests(args.test_dir, args.suffix))
    with concurrent.futures.ProcessPoolExecutor() as executor:
        for test_rel_path, diff in zip(test_rel_paths, executor.map(cn.get_diff, test_rel_paths)):
            if diff:
                failed_tests += 1
                sys.stderr.writelines(diff)
            if not args.quiet:
                if diff:
                    print('\033[31m[ FAILED ]\033[m %s' % test_rel_path)
                else:
                    print('\033[32m[ PASSED ]\033[m %s' % test_rel_path)
    sys.exit(min(failed_tests, 1))
    return

# top level
parser = argparse.ArgumentParser(description="Script for running CN proof tests.")
parser.set_defaults(func=(lambda _: parser.parse_args(['-h'])))
parser.add_argument('--test-dir', help='Directory of tests.', default='tests/cn')

parser.add_argument('--cn', default='cn')
parser.add_argument('--timeout', default=60)
parser.add_argument('--suffix', help='Uniquely identifying suffix of a file in the test directory.')
parser.add_argument('--quiet', help='Output unified format patches for the failing tests.',
        action='store_true')
parser.set_defaults(func=run_tests)

# parse args and call func (as set using set_defaults)
args = parser.parse_args()
args.func(args)

