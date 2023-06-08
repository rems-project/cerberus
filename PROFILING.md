# Profiling

For profiling Cerberus OCaml code could be instrumented with
[Landmarks](https://github.com/LexiFi/landmarks)

## Building

To use profiling you need to build with profiling support enabled using the following command:

`make PROFILING=true`

## Running

For example, to run Cerberus for CHERI C with profiling enabled:

`dune exec --workspace=dune-workspace.profiling --context profiling-auto --no-print-directory --display=quiet --auto-promote --root=$pwd cerberus-cheri-coq -- example.c`

To run it without profiling:

`dune exec --no-print-directory --display=quiet --auto-promote --root=$pwd cerberus-cheri-coq -- example.c`

