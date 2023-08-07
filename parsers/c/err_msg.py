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

def check(cond, f, *args, **kwargs):
    if not cond:
        eprint(f'line {f.get_count()}: ', *args, then_exit=True, **kwargs)

class CountLines:

    def __init__(self, f):
        self.count = 0
        self.file = f

    def get_line(self):
        self.count += 1
        line = self.file.readline()
        return line

    def get_count(self):
        return self.count

# Based on .message file format: http://gallium.inria.fr/~fpottier/menhir/manual.html#sec69
# See examples at the end of the file
def process_entry(f):

    output = []
    line = f.get_line()

    while line == '\n':
        output.append(line)
        line = f.get_line()

    # check for end of the file
    if not line:
        return output

    # otherwise it is the input sentence (first non-blank line)
    output.append(line)

    # check for any auto-generated comments (for the default error-message)
    auto_gen_comments = []
    line = f.get_line()
    while line.startswith('##'):
        auto_gen_comments.append(line)
        line = f.get_line()
    output += auto_gen_comments

    # skip over any other sentences or comments in entry
    while line != '\n' or line.startswith('#'):
        output.append(line)
        line = f.get_line()

    comment_or_blank = [ line ]
    line = f.get_line()
    while line == "\n" or line.startswith('#'):
        comment_or_blank.append(line)
        line = f.get_line()
    output += comment_or_blank

    err_msg = line

    # easy case - only one production (exactly 8 auto-gen lines) at line 4
    if len(auto_gen_comments) == 8 and err_msg == "<YOUR SYNTAX ERROR MESSAGE HERE>\n":
        # split the rule
        parts = auto_gen_comments[3][3:].split("->", 1)
        len_parts = len(parts)
        check(len_parts == 2, f,  f'(len_parts := {len_parts}) != 2')
        head = parts[0].strip()

        # split the body based on the position signified by '.'
        parts = parts[1].split('.', 1)
        len_parts = len(parts)
        check(len_parts == 2, f,  f'(len_parts := {len_parts}) != 2')
        seen = parts[0].strip()
        expected = re.sub("\\[.*", "", parts[1]).strip()

        if seen:
            # When we use the incremental parser, we can expand the used tokens:
            # https://gitlab.inria.fr/fpottier/menhir/-/blob/master/demos/calc-syntax-errors/calc.ml
            # seen = list(enumerate(seen.split(' ')))
            # seen.reverse()
            # seen = ' '.join([ f'${i}' for i,_ in seen ])
            err_msg = f'parsing "{head}": seen "{seen}", expecting "{expected}"\n'
        else:
            err_msg = f'parsing "{head}": expected "{expected}"\n'

    output.append(err_msg)
    return output

def for_file(args):
    if sys.version_info < (3, 8, 10):
        eprint("python version >= 3.8 required")

    try:
        with open(args.err_msg_file, 'r') as f:
            output = []
            count_lines = CountLines(f)
            while entry := process_entry(count_lines):
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

example1 = '''
grammar: TYPE UID
# This hand-written comment concerns just the sentence above.
grammar: TYPE OCAMLTYPE UID PREC
# This hand-written comment concerns just the sentence above.

# This hand-written comment concerns both sentences above.

Ill-formed declaration.
Examples of well-formed declarations:
  %type <Syntax.expression> expression
  %type <int> date time
'''

example2 = '''
grammar: TYPE UID
##
## Ends in an error in state: 1.
##
## declaration -> TYPE . OCAMLTYPE separated_nonempty_list(option(COMMA),
##   strict_actual) [ TYPE TOKEN START RIGHT PUBLIC PERCENTPERCENT PARAMETER
##   ON_ERROR_REDUCE NONASSOC LEFT INLINE HEADER EOF COLON ]
##
## The known suffix of the stack is as follows:
## TYPE
##
# This hand-written comment concerns just the sentence above.
#
grammar: TYPE OCAMLTYPE UID PREC
##
## Ends in an error in state: 5.
##
## strict_actual -> symbol . loption(delimited(LPAREN,separated_nonempty_list
##   (COMMA,strict_actual),RPAREN)) [ UID TYPE TOKEN START STAR RIGHT QUESTION
##   PUBLIC PLUS PERCENTPERCENT PARAMETER ON_ERROR_REDUCE NONASSOC LID LEFT
##   INLINE HEADER EOF COMMA COLON ]
##
## The known suffix of the stack is as follows:
## symbol
##
# This hand-written comment concerns just the sentence above.

# This hand-written comment concerns both sentences above.

Ill-formed declaration.
Examples of well-formed declarations:
  %type <Syntax.expression> expression
  %type <int> date time
'''

