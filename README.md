Cerberus C semantics
=====


Web interfaces, papers, and web page
---

See <https://www.cl.cam.ac.uk/~pes20/cerberus/>.



Build instructions for the CLI
---

To build Cerberus, you need opam (>= 2.0.0, see [here](https://opam.ocaml.org/doc/Install.html) to install) and OCaml (>= 4.07).

First set up additional repositories for Coq packages:

```bash
opam repo add --this-switch coq-released https://coq.inria.fr/opam/released
opam pin -n coq-struct-tact https://github.com/uwplse/StructTact.git
```

Sail coq libraries needs to be pinned manually. To do so:

```git clone git@github.com:rems-project/sail.git
cd sail/
git checkout 57b8acfad416014c38b47e7a5d134120a9c14999
cd lib/coq
opam install .
```

Then, install `coq-stdpp-unstable` by doing:
- `git clone https://gitlab.mpi-sws.org/iris/stdpp.git` in a separate directory (eg, in the parent directory of `cerberus`)
- `cd stdpp; ./make-package stdpp_unstable` to build `stdpp_unstable`
- `./make-package stdpp_unstable install` to install it
(in the future, the build&install commands should be replaced by `opam install coq-stdpp-unstable`)

`cd` back to the root of `cerberus` and install the remaining dependencies (including `lem` and `menhir`) using opam:

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
* cohttp    (2.5.5)
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



People
------

Contributors:
<ul>
<li>  <a href="http://www.cl.cam.ac.uk/users/km569">Kayvan Memarian</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/users/cp526">Christopher Pulte</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/users/vb358">Victor B. F. Gomes</a></li>
<li>  <a href="https://www.csail.mit.edu/person/stella-lau">Stella Lau</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/users/kn307">Kyndylan Nienhuis</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/~jm614">Justus Matthiesen</a></li>
<li>  <a href="http://www.jchl.co.uk">James Lingard</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/~dc552">David Chisnall</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/~rnw24">Robert N. M. Watson</a></li>
<li>  <a href="http://www.cl.cam.ac.uk/~pes20">Peter Sewell</a></li>
</ul>

The main Cerberus developer is Kayvan Memarian.
The experimental CN backend is by Christopher Pulte.
Victor Gomes made substantial contributions across the system, and Stella Lau was the main developer of Cerberus BMC. 
Kyndylan Nienhuis worked on the operational semantics for C11
concurrency. 
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
