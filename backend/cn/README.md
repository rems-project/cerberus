# CN

CN is a tool for verifying that C code is free of undefined behaviour and meets
user-written specifications of its ownership and functional correctness, and for translating those specifications into
C assertions that can be checked at runtime on concrete test cases.

## Papers


<ul>

<li> <a name="fulminate-popl2025"></a> 
   <a href="http://www.cl.cam.ac.uk/users/pes20/cn-testing-popl2025.pdf">Fulminate: Testing CN Separation-Logic Specifications in C</a>.
 Rini Banerjee, Kayvan Memarian, Dhruv Makwana, Christopher Pulte, Neel Krishnaswami, and Peter Sewell.
 In POPL 2025.
[
<a href="http://dx.doi.org/10.1145/3704879">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/users/pes20/cn-testing-popl2025.pdf">pdf</a> 
]
</li>


<li>
<a name="2023-popl-cn"></a>
<a href="http://www.cl.cam.ac.uk/users/pes20/cn-draft.pdf">CN: Verifying systems C code with separation-logic refinement types</a>.
 Christopher Pulte, Dhruv&nbsp;C. Makwana, Thomas Sewell, Kayvan Memarian, Peter Sewell, and Neel Krishnaswami.
 In POPL 2023.
[
<a href="http://dx.doi.org/10.1145/3571194">doi</a>&nbsp;| 
<a href="https://www.cl.cam.ac.uk/~cp526/popl23.html">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/users/pes20/cn-draft.pdf">pdf</a>
]
</li>
</ul>

## Tutorial

See the [tutorial documentation](https://rems-project.github.io/cn-tutorial/).

## Installation

Below are the installation instructions for installing Cerberus, CN,
and their dependencies.


1. Install make, git, GMP library, pkg-config and either/both Z3 or CVC5.
   On an Ubuntu system this is done via
   ```
   sudo apt install build-essential libgmp-dev pkg-config z3
   ```
   Note: there is a [known bug with Z3 version
   4.8.13](https://github.com/rems-project/cerberus/issues/663) (the default on
   Ubuntu 22.04) so you may wish to install Z3 via opam later for a more
   up-to-date version. Z3 that is provided in the docker images is sufficiently up-to-date.

2. Install the opam package manager for OCaml:
   https://ocaml.org/docs/installing-ocaml#install-opam.
   On Ubuntu, `sudo apt install opam`.

3. Initialise opam with a recent version of OCaml (the CI builds with 4.14.1,
   CN developers use 5.2.0).
   ```
   opam init --yes --compiler=5.2.0
   ````

4. Clone the Cerberus repo (which includes CN):
   ```
   git clone https://github.com/rems-project/cerberus.git
   ```

5. For CN end users, who don't want to tinker with CN locally:
   ```
   opam install --yes ./cerberus.opam ./cerberus-lib.opam ./cn.opam # z3 for a more recent version
   ```

6. For CN developers:
   ```
   opam install --deps-only ./cerberus.opam ./cerberus-lib.opam ./cn.opam ocamlformat.0.26.2 # one time
   make install_cn # after any edits
   ```
   which installs Cerberus, CN (as both a library and an executable), and
   dependencies.

## Contributing

Please see our [contributing
guide](https://github.com/rems-project/cerberus/blob/master/backend/cn/CONTRIBUTING.md)
for logistics and our [onboarding
guide](https://github.com/rems-project/cerberus/blob/master/backend/cn/ONBOARDING.md)
for learning the code base.

