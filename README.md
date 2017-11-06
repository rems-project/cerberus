Cerberus
=====

Installation
---

### LEM

Install `lem` (you might also need `libgmp`):

```bash
$ git clone https://bitbucket.org/Peter_Sewell/lem.git
$ cd lem
$ make
```

Set `LEM_PATH` to `lem` directory and include it in your path:

```bash
$ export LEM_PATH=/home/<path>/lem
$ export PATH=$LEM_PATH:$PATH
```

### Ocaml and opam 

Install `ocaml` (at least 4.02.0) and `opam`.
Then using opam, install:

* ocamlfind (tested with 1.5.3)
* cmdliner  (tested with 0.9.5)
* menhir    (tested with 20130912)
* pprint    (tested with 20140424)
* zarith    (tested with 1.4.1)

```bash
$ opam install ocamlfind cmdliner menhir pprint zarith
```

### Z3

```bash
$ git clone https://github.com/Z3Prover/z3.git
$ cd z3
$ python scripts/mk_make.py --ml
$ cd build
$ make
$ sudo make install
```

### Cerberus

```bash
$ hg clone https://bitbucket.org/Peter_Sewell/csem
$ cd csem
$ make
```

Set `CERB_PATH` and include it to your `PATH`:

```bash
$ export CERB_PATH=/home/<path>/csem
$ export PATH=$CERB_PATH:$PATH
```

Run and have fun!

```bash
$ cerberus --help
```

Requirements for the graph generation
----

  * pyparsing (can be installed by running "easy_install pyparsing")
  * latex preview package (on debian: "apt-get install preview-latex-style", on mac with texlive: "tlmgr install preview")
  * dot2tex (code.google.com/p/dot2tex/)
