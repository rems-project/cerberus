# Fulminate

Fulminate is a tool for translating CN specifications into C runtime assertions, for checking on concrete test inputs.

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

