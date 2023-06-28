#!/usr/bin/env python3
# This is a short script to run on a FRESH instance of a Menhir auto-generated .messages file.
# It reads the file, fills in the easy error-messages and then writes the output to stdout.
# It has assertions all over the place to check that the input really is as expected.

import argparse, os, re, sys

from pathlib import Path

def eprint(*args, then_exit=True, **kwargs):
    print(*args, file=sys.stderr, **kwargs)
    if then_exit:
        exit(1)

def process_entry(f):
    # input sentence
    line = f.readline()
    if not line:
        return []

    # input sentence
    assert line != "\n"
    output = [ line ]

    auto_gen_comments = []
    line = f.readline()
    while line.startswith("##"):
        auto_gen_comments.append(line)
        line = f.readline()

    auto_gen_comments_len = len(auto_gen_comments)
    assert auto_gen_comments_len >= 8
    output += auto_gen_comments

    # default error message
    assert line == "\n"
    output_line = f.readline()
    assert f.readline() == "\n"

    if auto_gen_comments_len == 8 and output_line == "<YOUR SYNTAX ERROR MESSAGE HERE>\n":
        # easy case
        parts = auto_gen_comments[3][3:].split("->", 1)
        prod = parts[0].strip()
        parts = parts[1].split('.', 1)
        assert len(parts) == 2
        seen = parts[0].strip()
        expected = re.sub("\\[.*", "", parts[1]).strip()
        if seen:
            # When we use the incremental parser, we can expand the used tokens:
            # https://gitlab.inria.fr/fpottier/menhir/-/blob/master/demos/calc-syntax-errors/calc.ml
            # seen = list(enumerate(seen.split(' ')))
            # seen.reverse()
            # seen = ' '.join([ f'${i}' for i,_ in seen ])
            output_line = f'parsing "{prod}": seen "{seen}", expecting "{expected}"\n' 
        else:
            output_line = f'parsing "{prod}": expected "{expected}"\n' 

    output += ["\n", output_line, "\n"]
    return output

def for_file(args):
    try:
        with open(args.err_msg_file, 'r') as f:
            output = []
            while entry := process_entry(f):
                output += entry
            print(*output, sep='', end='')
    except FileNotFoundError as e:
        eprint(f'File \'{args.err_msg_file}\' not found.')

# top level
parser = argparse.ArgumentParser(description="Helper script for writing error messages.")
parser.add_argument('err_msg_file', help='Name of .messages file')
parser.set_defaults(func=for_file)

# Parse args and call func (as set using set_defaults)
args = parser.parse_args()
args.func(args)

