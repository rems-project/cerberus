# Ocaml backend for Cerberus

## Generate an ocaml file from C files

```bash
  $ cerberus-ocaml file1.c file2.c ... filen.c -o app.ml
```

## Compile the ml file

```bash
  $ OCAMLPATH=$CERB_PATH/_lib ocamlfind ocamlopt $CERB_PATH/backend/driver/_build/common/cerberus_cstubs.o -linkpkg -package pprint,yojson,unix,lem,util,ppx_sexp_conv,sexplib,sibylfs,concrete,rt-ocaml app.ml -o app
  $ ./app
```

## Or use Cbuild

From `CSEM_PATH` run `make cbuild`.

```bash
  $ cbuild file1.c file2.c ... filen.c -o app
  $ ./app
```