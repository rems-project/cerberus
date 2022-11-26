# Profiling

For profiling Cerberus OCaml code could be instrumented with
[Landmarks](https://github.com/LexiFi/landmarks)

## Building

`make profiling-build`

## Running

`dune exec --context profiling-auto --no-print-directory --display=quiet --auto-promote --root=~/src/cerberus <cmd> -- <args> <file.c>`

