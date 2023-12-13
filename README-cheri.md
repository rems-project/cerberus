Building and running instructions for Cerberus-CHERI

## Docker

Execute `test.c` using CHERI C semantics:

`docker run -v $HOME/tmp:/mnt -it vzaliva/cerberus-cheri cerberus-cheri --exec /mnt/test.c`

Execute `test.c` using ISO C semantics:

`docker run -v $HOME/tmp:/mnt -it vzaliva/cerberus-cheri cerberus --exec /mnt/test.c`

Print __Core__ elaboration for `test.c` using CHERI C semantics:

`docker run -v $HOME/tmp:/mnt -it vzaliva/cerberus-cheri cerberus-cheri --pp=core --exec /mnt/test.c`

Print _Core_ elaboration for `test.c` using ISO C semantics:

`docker run -v $HOME/tmp:/mnt -it vzaliva/cerberus-cheri cerberus --pp=core --exec /mnt/test.c`

## Local install

To build Cerberus, you need opam (>= 2.0.0, see [here](https://opam.ocaml.org/doc/Install.html) to install) and OCaml (>= 4.12.0).

First set up additional repositories for Coq and Iris packages:

```sh
opam repo add --this-switch coq-released https://coq.inria.fr/opam/released
opam pin -n coq-struct-tact https://github.com/uwplse/StructTact.git
opam repo add --this-switch iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin -n coq-sail https://github.com/rems-project/coq-sail.git
opam pin -n coq-cheri-capabilities https://github.com/rems-project/coq-cheri-capabilities.git
```

Install the remaining dependencies (including `lem` and `menhir`) using opam:

```sh
opam install --deps-only ./cerberus-cheri.opam
```

Then to build Cerberus-CHERI:

```bash
make cheri
```

To install Cerberus-CHERI:

```bash
opam pin add -n cerberus-lib .
opam pin add -n cerberus-cheri .
opam install cerberus-cheri
```
