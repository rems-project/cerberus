Build instructions for Cerberus-CHERI

To build Cerberus, you need opam (>= 2.0.0, see [here](https://opam.ocaml.org/doc/Install.html) to install) and OCaml (>= 4.12.0).

First set up additional repositories for Coq and Iris packages:

```bash
opam repo add --this-switch coq-released https://coq.inria.fr/opam/released
opam pin -n coq-struct-tact https://github.com/uwplse/StructTact.git
opam repo add --this-switch iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin -n coq-sail https://github.com/rems-project/coq-sail.git
opam pin -n coq-cheri-capabilities https://github.com/rems-project/coq-cheri-capabilities.git
```

Install the remaining dependencies (including `lem` and `menhir`) using opam:

```bash
opam install --deps-only ./cerberus-cheri.opam
```

Then to build Cerberus-CHERI:

```bash
make cheri
```