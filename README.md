Cerberus C semantics - Snapshot
=====

This is a pre-release snapshot of the sources for the command-line interface version of the Cerberus C semantics <https://www.cl.cam.ac.uk/~pes20/cerberus/>. It is made available to support the release of RefinedC <https://plv.mpi-sws.org/refinedc/> and for no other purpose; it should not be used for development.


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
