# CN Coq Proof assistant intergration

## Installation

You need Opam >= 2.0.0 OCaml >= 4.12.0 Coq >= 8.18.0.
(>= 4.12.0). The developers are currently using OCaml 5.2.0 and Coq 8.19.2.

It is recommended to create a new switch for CN-Coq:

```shell
opam switch create cerberus-cn 5.2.0
``` 

First set up additional repositories for Coq and Iris packages:

```shell
opam repo add --this-switch coq-released https://coq.inria.fr/opam/released
opam pin -ny coq-struct-tact https://github.com/uwplse/StructTact.git
opam repo add --this-switch iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

Install the remaining dependencies using opam:

```shell
opam pin add -ny cerberus-lib .
opam pin add -ny cerberus-cheri .
opam pin add -ny cn .
opam install --deps-only ./cn-coq.opam
```

Then to build Cn-Coq:

```shell
make cn-coq
```

To install:

```shell
make install-cn-coq
```

