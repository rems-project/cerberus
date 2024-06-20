# CN

CN is tool for verifying C code is free of undefined behaviour and meets
user-written specifications. It can also convert those specifications into
assertions to be checked at runtime during test cases.

## Installation

Below are the installation instructions for installing Cerberus, CN,
and their dependencies.


1. Install a recent version of OCaml (we are using 5.0.0) and the opam
package manager for OCaml, following the instructions at
<https://ocaml.org/docs/install.html>. (Remember to initialise opam
via `opam init` after the installation of opam.)

2. Install the GMP and MPFR libraries, and Python (a dependency of
   Z3). On a Ubuntu system this is done via `sudo apt install libgmp-dev libmpfr-dev python2.7` .

3. Install the `dune` OCaml build system and Lem via

    ```
    opam install dune lem
    ```

4. Obtain a copy of Cerberus (including CN) by running

    ```
    git clone https://github.com/rems-project/cerberus.git
    ```

5. In the downloaded `cerberus` directory run the following opam
   command to install CN's opam-package dependencies, including
   Z3. (Installation of Z3 usually takes relatively long.)

    ```
    opam install --deps-only ./cerberus-lib.opam ./cn.opam
    ```

6. then run

   ```
   make install
   ```

   and finally

   ```
   make install_cn
   ```

   which installs Cerberus, CN, and dependencies.

## Contributing

Please see our [contributing
guide](https://github.com/rems-project/cerberus/blob/master/backend/cn/ONBOARDING.md)
for logistics and our [onboarding
guide](https://github.com/rems-project/cerberus/blob/master/backend/cn/ONBOARDING.md)
for learning the code base.

## Funding Acknowledgements

TODO (PS?)
