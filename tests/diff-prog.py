#!/usr/bin/env python3

import os, sys, re, subprocess, json, difflib, argparse, concurrent.futures, math

def eprint(*args, then_exit=True, **kwargs):
    print('Error:', *args, file=sys.stderr, **kwargs)
    if then_exit:
        exit(1)

def time_cmd(cmd):
    return ["/usr/bin/time", "--quiet", "--format", "%e"] + cmd

class Prog:

    def __init__(self, opts, config):
        self.prog = opts.prog
        self.args = config['args']
        self.print_cmd = opts.dry_run or opts.verbose
        self.run_cmd = not opts.dry_run
        self.timeout = config['timeout']
        self.name = config['name']

    def run(self, test_rel_path):
        cmd = time_cmd([self.prog] + self.args + [test_rel_path])
        if self.print_cmd:
            print(' '.join(cmd))
        if self.run_cmd:
            return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=self.timeout)
        else:
            return None

    def output(self, test_rel_path):
        try:
            completed = self.run(test_rel_path);
            lines = completed.stdout.splitlines(True)
            time = float(lines[-1])
            return { 'time': time, 'lines' : [("return code: %d\n" % completed.returncode)] + lines[:-1] }
        except subprocess.TimeoutExpired:
            return { 'time': float(self.timeout), 'lines': ["TIMEOUT\n"] }

    def get_diff(self, test_rel_path):
        expect_path = test_rel_path + '.' + self.name
        if not os.path.isfile(expect_path):
            open(expect_path, 'w')
        with open(expect_path, 'r') as expect:
            try:
                output = self.output(test_rel_path)
                diff = list(difflib.unified_diff(expect.readlines(), output['lines'], expect_path, expect_path))
                time = output['time']
                return { 'diff': diff, 'time': time }
            except AttributeError: # dry run
                return { 'diff': False, 'time': .0 }

def test_files(test_dir, matcher):
    if not os.path.isdir(test_dir):
        eprint(f"'{test_dir}' not a directory")
    for root, _, files in os.walk(test_dir):
        for filename in files:
            if matcher.match(filename) is not None:
                yield os.path.join(root, filename)

def filter_tests(test_dir, suffix, matcher):
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

def format_timing(name, value):
    return { 'name': name, 'unit': 'Seconds', 'value': value }

def run_tests(prog, test_rel_paths, quiet, max_workers):
    test_rel_paths = list(test_rel_paths)
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        failed_tests = 0
        timings = []
        for test_rel_path, outcome in zip(test_rel_paths, executor.map(prog.get_diff, test_rel_paths), strict=True):
            time = outcome['time']
            diff = outcome['diff']
            timings.append(format_timing(test_rel_path, time))
            if not prog.run_cmd:
                continue
            pass_fail = '\033[32m[ PASSED ]\033[m'
            if diff:
                failed_tests += 1
                sys.stderr.writelines(diff)
                pass_fail = '\033[31m[ FAILED ]\033[m'
            if not quiet:
                print('%s %s' % (pass_fail, test_rel_path))
        return { 'code': min(failed_tests, 1), 'timings': timings }

def output_bench(name, timings):
    total = { 'name': 'Total benchmark time', 'unit': 'Seconds', 'value':  math.fsum(timing['value'] for timing in timings) }
    with open(('benchmark-data-%s.json' % name), 'w') as f:
        json.dump([total] + timings, f, indent=2)

def main(opts):
    with open(opts.config) as config_file:
        config = json.load(config_file)
        prog = Prog(opts, config)
        files = filter_tests(test_dir=os.path.dirname(opts.config), suffix=opts.suffix, matcher=re.compile(config['filter']))
        result = run_tests(prog, test_rel_paths=files, quiet=opts.quiet, max_workers=(1 if opts.bench else None))
        if opts.bench:
            output_bench(config['name'], result['timings'])
        return result['code']

# top level
parser = argparse.ArgumentParser(description="Script for running an executable and diffing the output.")
parser.set_defaults(func=(lambda _: parser.parse_args(['-h'])))
parser.add_argument('prog')
parser.add_argument('config', help='Path to JSON config file: { "name": string; "args": string list; "filter": python regexp; "timeout": seconds }.')
parser.add_argument('-v', '--verbose', help='Print commands used.', action='store_true')
parser.add_argument('--dry-run', help='Print but do not run commands.', action='store_true')
parser.add_argument('--suffix', help='Uniquely identifying suffix of a file in the test directory.')
parser.add_argument('--quiet', help='Don\'t show tests completed so far on std out.', action='store_true')
parser.add_argument('--bench', help='Output a JSON file with benchmarks, including total time.', action='store_true')
parser.set_defaults(func=main)

# parse args and call func (as set using set_defaults)
opts = parser.parse_args()
exit(opts.func(opts))
