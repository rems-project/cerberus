#!/usr/bin/env python3

import os, sys, re, subprocess, json, difflib, argparse, concurrent.futures

def eprint(*args, then_exit=True, **kwargs):
    print('Error:', *args, file=sys.stderr, **kwargs)
    if then_exit:
        exit(1)

class Prog:

    def __init__(self, args, config):
        self.prog = args.prog
        self.args = config['args']
        self.print_cmd = args.dry_run or args.verbose
        self.run_cmd = not args.dry_run
        self.timeout = config['timeout']
        self.name = config['name']
        self.matcher = re.compile(config['filter'])
        self.suffix = args.suffix

    def run(self, test_rel_path):
        cmd = [self.prog] + self.args + [test_rel_path]
        if self.print_cmd:
            print(' '.join(cmd))
        if self.run_cmd:
            return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=self.timeout)
        else:
            return None

    def output(self, test_rel_path):
        try:
            completed = self.run(test_rel_path);
            result = ("return code: %d\n%s" % (completed.returncode, completed.stdout))
        except subprocess.TimeoutExpired:
            result = "TIMEOUT\n"
        return result.splitlines(True)

    def get_diff(self, test_rel_path):
        expect_path = test_rel_path + '.' + self.name
        if not os.path.isfile(expect_path):
            open(expect_path, 'w')
        with open(expect_path, 'r') as expect:
            try:
                return list(difflib.unified_diff(expect.readlines(), self.output(test_rel_path), expect_path, expect_path))
            except AttributeError: # dry run
                return False

def test_files(test_dir, matcher):
    if not os.path.isdir(test_dir):
        eprint(f"'{test_dir}' not a directory")
    for root, _, files in os.walk(test_dir):
        for filename in files:
            if matcher.match(filename) is not None:
                yield os.path.join(root, filename)


def filter_tests(**kwargs):
    test_dir = kwargs['test_dir']
    suffix = kwargs['suffix']
    matcher = kwargs['matcher']
    inputs = test_files(test_dir, matcher)
    if suffix is not None:
        inputs = list(filter(lambda x : x.endswith(suffix), inputs))
        inputs_len = len(inputs)
        if inputs_len > 1:
            eprint(f'more than one file matching *{suffix} found in {test_dir}', then_exit=False)
            eprint(inputs)
        elif inputs_len == 0:
            eprint(f'*{suffix} not found in {test_dir}')
    return inputs

def run_tests(prog, **kwargs):
    quiet = kwargs['quiet']
    test_rel_paths = list(filter_tests(**kwargs))
    with concurrent.futures.ProcessPoolExecutor() as executor:
        failed_tests = 0
        for test_rel_path, diff in zip(test_rel_paths, executor.map(prog.get_diff, test_rel_paths)):
            if not prog.run_cmd:
                continue
            pass_fail = '\033[32m[ PASSED ]\033[m'
            if diff:
                failed_tests += 1
                sys.stderr.writelines(diff)
                pass_fail = '\033[31m[ FAILED ]\033[m'
            if not quiet:
                print('%s %s' % (pass_fail, test_rel_path))
        return min(failed_tests, 1)

def main(args):
    with open(args.config) as config_file:
        config = json.load(config_file)
        prog = Prog(args, config)
        return run_tests(prog, test_dir=os.path.dirname(args.config), suffix=args.suffix, matcher=re.compile(config['filter']), quiet=args.quiet)

# top level
parser = argparse.ArgumentParser(description="Script for running an executable and diffing the output.")
parser.set_defaults(func=(lambda _: parser.parse_args(['-h'])))
parser.add_argument('-v', '--verbose', help='Print commands used.', action='store_true')
parser.add_argument('--dry-run', help='Print but do not run commands.', action='store_true')
parser.add_argument('config', help='Path to JSON config file: { "name": string; "args": string list; "filter": python regexp; "timeout": seconds }.')

parser.add_argument('prog')
parser.add_argument('--suffix', help='Uniquely identifying suffix of a file in the test directory.')
parser.add_argument('--quiet', help='Don\'t show tests completed so far on std out.', action='store_true')
parser.set_defaults(func=main)

# parse args and call func (as set using set_defaults)
args = parser.parse_args()
args.func(args)

