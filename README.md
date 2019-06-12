Cerberus
=====

Cerberus CLI
---

### Ocaml, opam and common dependencies

Install `ocaml` (at least 4.06.0) and `opam`.
Then using opam, install Cerberus dependencies:

* ocamlfind (tested with 1.7.3-1)
* cmdliner  (tested with 1.0.2)
* menhir    (tested with 20171212)
* pprint    (tested with 20171003)
* yojson    (tested with 1.4.1)

LEM dependencies:
* zarith    (tested with 1.7)

And SibylFS dependencies:
* ppx_sexp_conv (tested with 113.09.00)
* sexplib       (tested with 113.00.00)

```bash
$ opam install ocamlfind cmdliner menhir pprint yojson zarith ppx_sexp_conv sexplib
```

### LEM

Install `lem`

```bash
$ git clone https://github.com/rems-project/lem.git
$ cd lem
$ make
$ cd ocaml-lib; sudo make install
```

Set `LEM_PATH` to `lem` directory and include it in your path:

```bash
$ export LEM_PATH=/home/<path>/lem
$ export PATH=$LEM_PATH:$PATH

```

### Set Enviroment

Set `CERB_PATH` and include it to your `PATH`:

```bash
$ export CERB_PATH=/home/<path>/cerberus
$ export PATH=$CERB_PATH:$PATH
```

### Cerberus with the Concrete Memory Model

Just run:

```bash
$ make
```

It installs the internal libraries in `_lib` and the CLI binary `cerberus`.

Run and have fun!

```bash
$ cerberus --help
```

### Cerberus with the Symbolic Memory Model

Using `opam`, install the following extra dependencies:

* z3        (tested with 4.7.1)
* angstrom  (tested with 4.06.0)

```bash
$ opam install z3 angstrom
```

And run:

```bash
$ make cerberus-symbolic
```

It installs the internal libraries in `_lib` and the CLI binary `cerberus-symbolic`.

Run and have fun!

```bash
$ cerberus-symbolic --help
```

Cerberus BMC
---

Install the common dependencies and the following extra ones:

* z3        (tested with 4.7.1)
* angstrom  (tested with 4.06.0)

Then run:

```bash
$ make cerberus-bmc
```

It installs the internal libraries in `_lib` and the CLI binary `cerberus-bmc`.

Run and have fun!

```bash
$ cerberus-bmc --help
```

Cerberus Web/UI
---

Install the common dependencies and the following extra ones:

* z3        (tested with 4.7.1)
* angstrom  (tested with 4.06.0)
* lwt       (tested with 3.3.0)
* cohttp    (tested with 1.1.0)
* base64    (tested with 2.2.0)
* cohttp-lwt-unix (tested with 1.0.3)
* ezgzip    (tested with 0.2.0)

Then run:

```bash
$ make web
```

It installs all the available web instances as `webcerb.*` and the web server `cerberus-webserver`.

To build the UI, install node package manager `npm` and run:

```bash
$ make ui
```

Edit the generated `config.json`.

Run and have fun!

```bash
$ cerberus-server --help
```


All targets
---

You can also compile all the targets with:

```bash
$ make all
```

Internal Libraries
----

### Util

These are utility modules that do not depend on any model (any LEM file). They
are located at `./util`. And can be built with:

```bash
$ make util
```

### SibylFS

SibylFS: formal specification and oracle-based testing for POSIX and real-world
file systems. More information can be obtained at
[https://sibylfs.github.io](https://sibylfs.github.io).

The files are located at `./sibylfs`. And can be built with:

```bash
$ make sibylfs
```
