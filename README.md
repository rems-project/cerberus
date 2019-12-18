Cerberus C semantics
=====

Some example usage of the CLI
---

### Running the pipeline without executing:

```bash
$ cerberus file1.c ... fileN.c
```
This will elaborate the C translation units to Core programs, and link them, before returning silently.

Include directories can be added with the usual ```-I```, and macros can be forwarded to the preprocessor using ```-D``` (and unset with ```-U```).

The **ail** intermediate representation, and the **core** program can be printed by passing them as argument to ```--pp=```.

The C abstract syntax (**cabs**), and the **ail** AST can be printed by passing them as argument to ```--ast=```.


### Executing something
```bash
$ cerberus --exec file1.c ... fileN.c
```
This will look for a ```main()``` function and starts from there. To see the return value, or get a machine friendly collection of stdout and stderr, add ```--batch```.

### Passing command line arguments to the C program
```bash
$ cerberus --args="arg1","arg2" file.c
```

---

Various C programs can be found in ```tests/```



Building the Cerberus CLI
---

### Opam, Ocaml and dependencies

To build Cerberus you need `opam` (see [here](https://opam.ocaml.org/doc/Install.html) to install) and `ocaml` (>= 4.07).

You also need `lem`, which can be installed using opam from the rems-project repository:

```bash
$ opam repository add rems https://github.com/rems-project/opam-repository.git
$ opam install lem
```
Then using opam, install the following packages (the versions are ones that are known to work, older ones may also be fine):

* ocamlfind       (1.8.1)
* ocamlbuild      (0.14.0)
* pprint          (20180528)
* yojson          (1.7.0)
* ppx\_sexp\_conv (v0.13.0), this a dependency of SibylFS
* sexplib	        (v0.13.0), this a dependency of SibylFS
* ppx\_deriving	 (4.4), this a dependency of SibylFS
* cmdliner        (1.0.4)
* menhir			 (20190924)
* z3				 (4.8.6)

```bash
$ opam install ocamlfind ocamlbuild pprint yojson ppx_sexp_conv sexplib ppx_deriving cmdliner menhir z3
```

### Set Environment

Set `CERB_PATH` to that of the `cerberus-private` checkout and include it to your `PATH`:

```bash
$ export CERB_PATH=/home/<path>/cerberus-private/
$ export PATH=$CERB_PATH:$PATH
```

You also need to have C compiler accessible from the command ``cc``. Cerberus will make use of it of its preprocessor.


### Building with the concrete memory model

Just run:

```bash
$ make
```

It installs the internal libraries in `_lib` and the produces the CLI binary `cerberus`.

Run and have fun!

```bash
$ cerberus --help
```

### Building with the symbolic memory model

Using `opam`, install the following extra dependencies:

* z3        (4.8.6)
* angstrom  (4.06.0)

```bash
$ opam install z3 angstrom
```

And run:

```bash
$ make cerberus-symbolic
```

It installs the internal libraries in `_lib` and produces the CLI binary `cerberus-symbolic`.

Run and have fun!

```bash
$ cerberus-symbolic --help
```

Building Cerberus-BMC
---

Install the common dependencies and the following extra ones:

* z3        (4.8.6)
* angstrom  (4.06.0)

Then run:

```bash
$ make cerberus-bmc
```

It installs the internal libraries in `_lib` and the CLI binary `cerberus-bmc`.

Run and have fun!

```bash
$ cerberus-bmc --help
```

Building the web server
---

Install the common dependencies and the following extra ones:

* z3        (4.8.6)
* angstrom  (4.06.0)
* lwt       (3.3.0)
* cohttp    (1.1.0)
* base64    (2.2.0)
* cohttp-lwt-unix (1.0.3)
* ezgzip    (0.2.0)


presuming z3 and angstrom are already installed:

```bash
$ opam install lwt cohttp base64 cohttp-lwt-unix ezgzip
```

Then run:

```bash
$ make web
```

It installs all the available web instances as `webcerb.*` and the web server `cerberus-webserver`.

To build the UI, install node package manager `npm` (sudo apt install nodejs npm
) and run:

```bash
$ make ui
```

Edit the generated `config.json`.

Run and have fun!

```bash
$ cerberus-server --help
```

Building the abstract interpreter
---

Install the common dependencies and the APRON library (tested with 20160125).

```bash
$ opam install apron
```

Then run:

```bash
$ make absint
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
