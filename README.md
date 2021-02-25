Cerberus C semantics
=====

Build instructions for the CLI
---

To build Cerberus, you need opam (>= 2.0.0, see [here](https://opam.ocaml.org/doc/Install.html) to install) and OCaml (>= 4.07).

First install the dependencies (including `lem` and `menhir`) using opam:

```bash
$ opam install --deps-only .
```

Then build the CLI using:

```bash
$ make
```

The CLI can then be used either from the source directory using:

```bash
$ dune exec cerberus -- ARG1 .. ARGN
```

or, after doing `$ make install`, using the `cerberus` executable.

Basic usage
---

### Executing some translation units:
```bash
$ cerberus --exec file1.c ... fileN.c
```
This will elaborate to Core, link, look for a ```main()``` function, and start executing the Core from there. To see a printout of the return value, and to get a machine-friendly collection of stdout and stderr,
add the ```--batch``` argument.


### Passing command line arguments to the C program
```bash
$ cerberus --args="arg1","arg2" file.c
```

### Printing the intermediate representations
* The C abstract syntax (**Cabs**) and the **Ail** intermediate representation can be printed with  ```--ast=cabs``` and ```--ast=ail```.

* The **Ail** intermediate representation and the **Core** program can be pretty-printed with ```--pp=ail``` and ```--pp=core```.

### Running the elaborate-and-link pipeline without executing:

```bash
$ cerberus file1.c ... fileN.c
```
This will elaborate the C translation units to Core programs, and link them, before returning silently.

Include directories can be added with the usual ```-I```, and macros can be forwarded to the preprocessor using ```-D``` (and unset with ```-U```).

---

For more, see `cerberus --help`

---

Various C programs can be found in ```tests/```.


Building Cerberus-BMC
---

Install the common dependencies and the following extra ones:

* z3        (4.8.6)
* angstrom  (4.06.0)

```bash
$ opam install z3 angstrom
```

Then run:

```bash
$ make cerberus-bmc
```

---

To run:

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

Then:

```bash
$ make web
```

This installs all the available web instances as `webcerb.*` and the web server `cerberus-webserver`.

To build the UI, install node package manager `npm` (sudo apt install nodejs npm
) and:

```bash
$ make ui
```

Edit the generated `config.json`.

Run:

```bash
$ cerberus-server --help
```

Building the abstract interpreter
---

Install the common dependencies and the APRON library (tested with 20160125).

```bash
$ opam install apron
```

Then:

```bash
$ make absint
```

All targets
---

You can also compile all the targets with:

```bash
$ make all
```


Docker image
------------

```bash
$ make -f Makefile_docker
```
creates a Docker image than can be used for example with:
```bash
$ docker run --volume `PWD`:/data/ cerberus:0.1 tests/tcc/00_assignment.c --pp=core
```
This image contains all the source code.
