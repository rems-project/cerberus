# CN Testing

CN has testing capabilities available via the `cn test` subcommand.

## Overview

Currently, CN supports only per-function tests, but additional types of testing may become available in the future.

Running `cn test <filename.c>` generates C files with the testing infrastructure, the instrumented program under test, and a build script named `run_tests.sh`.
This script compiles the C files and runs the tests.

By default, running `cn test` will automatically run `run_tests.sh`, which produces a test executable `tests.out`.
This can be disabled by using the `--no-run` flag.

The output directory for these files can be set by using `--output-dir=<DIR>`.
If the directory does not already exist, it is created.

### Per-function tests

When testing, there are currently two types of tests, constant tests and generator-based tests.
For *each function with a body*, CN will create either a constant test or generator-based test.

If a function takes no arguments, does not use accesses on global variables, and is correct, it should always return the same value and free any memory it allocates.
In this case, a constant test is generated, which runs the function once and uses [Fulminate](FULMINATE_README.md) to check for post-condition violations.

In all other cases, it creates generator-based tests, which are in the style of property-based testing.
A "generator" is created, which randomly generates function arguments, values for globals accessed and heap states, all of which adhere to the given function's pre-condition.
It calls the function with this input and uses [Fulminate](FULMINATE_README.md) similar to the constant tests.

#### Understanding errors

Currently, the tool does not print out counterexamples, but this is [planned](https://github.com/rems-project/cerberus/issues/841).
Until then, `tests.out` can be run with the `--trap` flag in a debugger.
Since seeds are printed each time the tool runs, `--seed <seed>` can be used to reproduce the test case.
The debugger should automatically pause right before rerunning the failing test case.

#### Writing custom tests

There is currently no way to write custom property-based tests.
However, once lemmas can be tested, a lemma describing the desired property could be written to test it.

In terms of unit tests, one can simply define a function that performs the desired operations.
This function will get detected by `cn test` and turned into a constant test.
Any assertions that one would make about the result would have to be captured by the post-condition.
In the future, existing infrastructure like `cn_assert` might be adapted for general use.
