# Cerberus C semantics

[![CI](https://github.com/rems-project/cerberus/actions/workflows/ci.yml/badge.svg)](https://github.com/rems-project/cerberus/actions/workflows/ci.yml)


Web interfaces, papers, and web page
---

See <https://www.cl.cam.ac.uk/~pes20/cerberus/>.



Build instructions for the CLI
---

To build Cerberus, you need opam (>= 2.0.0, see [here](https://opam.ocaml.org/doc/Install.html) to install) and OCaml (>= 4.12.0).

First install the dependencies (including `lem` and `menhir`) using opam:

```bash
$ opam install --deps-only ./cerberus-lib.opam ./cerberus.opam
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

---
To fully remove all object and Lem generated files:

```
$ make distclean
```

To remove the object files, but keep the Lem generated files (allowing for faster build when only working on `.ml` files):

```
$ make clean
```


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

* angstrom  (0.15.0)

```bash
$ opam install angstrom
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

* lwt
* fpath           (0.7.3)
* ezgzip          (0.2.3)
* cohttp-lwt-unix (5.0.0)


```bash
$ opam install lwt fpath ezgzip cohttp-lwt-unix
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

Install the common dependencies and the APRON library (tested with v0.9.12).

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

Building CN
---
See https://github.com/rems-project/cerberus/blob/master/backend/cn/README.md


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



People
------

Contributors:
<ul>
<li>  <a href="https://www.cl.cam.ac.uk/~km569">Kayvan Memarian</a></li>
<li>  <a href="https://www.cl.cam.ac.uk/~cp526">Christopher Pulte</a></li>
<li>  <a href="https://www.cst.cam.ac.uk/people/tals4">Thomas Sewell</a></li>
<li>  <a href="https://www.cl.cam.ac.uk/~vb358">Victor B. F. Gomes</a></li>
<li>  <a href="https://people.csail.mit.edu/stellal/">Stella Lau</a></li>
<li>  <a href="https://www.cl.cam.ac.uk/~kn307/">Kyndylan Nienhuis</a></li>
<li>  <a href="https://www.cst.cam.ac.uk/people/dcm41">Dhruv Makwana</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/~jm614">Justus Matthiesen</a></li>
<li>  James Lingard</li>
<li>  <a href="https://www.cl.cam.ac.uk/~dc552">David Chisnall</a></li>
<li>  <a href="https://www.cl.cam.ac.uk/~rnw24">Robert N. M. Watson</a></li>
<li>  <a href="https://www.cl.cam.ac.uk/~pes20">Peter Sewell</a></li>
<li>  <a href="https://zaliva.org/">Vadim Zaliva</a></li>
</ul>

The main Cerberus developer is Kayvan Memarian.
Victor Gomes made substantial contributions across the system.
Kyndylan Nienhuis worked on the operational semantics for C11 concurrency. 
Stella Lau is the main developer of Cerberus BMC.
The CN backend is by Christopher Pulte and Thomas Sewell.
The CHERI memory model is by Vadim Zaliva.
Cerberus originated with Justus Matthiesen's 2010-11 Part II project
dissertation and his 2011-12 MPhil dissertation. James Lingard's
2013-14 MPhil dissertation developed a certifying translation
validator for simple C programs for the Clang front-end, w.r.t. the
Cerberus and Vellvm semantics. 


Funding
-----
This software was developed largely within the Rigorous Engineering of
Mainstream Systems (REMS) project at the University of Cambridge.  It
has received funding from the European Research Council (ERC) under
the European Union's Horizon 2020 research and innovation programme
(grant agreement No 789108, ELVER); the EPSRC Programme Grant REMS:
Rigorous Engineering of Mainstream Systems (EP/K008528/1); an EPSRC
Leadership Fellowship EP/H005633 (Sewell); a Gates Cambridge
Scholarship (Nienhuis); an MIT EECS Graduate Alumni Fellowship
(Lau); and Google. 
