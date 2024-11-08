# Fulminate

Fulminate is a tool for translating CN specifications into C runtime assertions, which can then be checked using concrete test inputs.

## Installation 

Fulminate is installed as part of the CN toolchain - see [README.md](README.md) for instructions.

## Running Fulminate

### Generating executable specifications

To produce a file instrumented with CN runtime assertions, run:

```bash
cn instrument <your-file>.c
```

This will produce three files: 

* `<your-file>-exec.c`, the instrumented source
* `cn.h`, a header file containing various definitions and prototypes, including C struct definitions representing CN datatypes, structs and records, as well as function prototypes for the various translated top-level CN functions and predicates.
* `cn.c`, a file that includes `cn.h` and provides definitions for the aforementioned prototypes


These are all produced in the directory the command was run from. Alternatively, one can provide an output directory for these three files (after creating the directory) using the `--output-dir` argument:


```bash
cn instrument <your-file>.c --output-dir <path/to/output/dir>
```

The translation tool injects the executable precondition right before the source function body, at the start of the given function; the executable postcondition into a label called `cn_epilogue`, which gets jumped to via a `goto` wherever there is a return statement in the source; and the executable assertions inplace, wherever they were defined in the source.

### Compiling, linking and running executable CN specifications

To compile and link the output files described in the above section, and also to run these examples on some manually-produced concrete inputs (i.e. via a handwritten `main` function), one can run the following commands:

```bash
export CHECK_SCRIPT="$OPAM_SWITCH_PREFIX/lib/cn/runtime/libexec/cn-runtime-single-file.sh"
$CHECK_SCRIPT <your-file>.c
```

This runs the `cn-runtime-single-file.sh` script from the CN runtime library on `<your-file>.c`, which generates the executable specification files, compiles and links these, and then runs the produced binary. This script is configurable with the `-n` option for disabling dynamic ownership checking and/or the `-q` option for running the script in quiet mode. This script can be found in `runtime/libcn/libexec` if you are interested in seeing the compile and link commands.

The compile command includes the `-g` flag for collecting debug information, which means gdb or lldb can be run on the produced binary for setting breakpoints, stepping in and out of functions in a given run, printing concrete variable values at specific points in the program run, etc. gdb can cause problems on Mac due to some certification-related issues, so for Mac users we recommend you use lldb.

