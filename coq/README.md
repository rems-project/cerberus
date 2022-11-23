This is variation on https://gitlab.mpi-sws.org/iris/stdpp to work embedded in a project that contains some files with the same names.

# Coq-std++ [[coqdoc]](https://plv.mpi-sws.org/coqdoc/stdpp/)

This project contains an extended "Standard Library" for Coq called coq-std++.
The key features of this library are as follows:

- It provides a great number of definitions and lemmas for common data
  structures such as lists, finite maps, finite sets, and finite multisets.
- It uses type classes for common notations (like `∅`, `∪`, and Haskell-style
  monad notations) so that these can be overloaded for different data structures.
- It uses type classes to keep track of common properties of types, like it
  having decidable equality or being countable or finite.
- Most data structures are represented in canonical ways so that Leibniz
  equality can be used as much as possible (for example, for maps we have
  `m1 = m2` iff `∀ i, m1 !! i = m2 !! i`). On top of that, the library provides
  setoid instances for most types and operations.
- It provides various tactics for common tasks, like an ssreflect inspired
  `done` tactic for finishing trivial goals, a simple breadth-first solver
  `naive_solver`, an equality simplifier `simplify_eq`, a solver `solve_proper`
  for proving compatibility of functions with respect to relations, and a solver
  `set_solver` for goals involving set operations.
- It is entirely dependency- and axiom-free.

## Side-effects

Importing std++ has some side effects as the library sets some global options.
Notably:

* `Generalizable All Variables`: This option enables implicit generalization in
  arguments of the form `` `{...}`` (i.e., anonymous arguments).  Unfortunately, it
  also enables implicit generalization in `Instance`.  We think that the fact
  that both behaviors are coupled together is a
  [bug in Coq](https://github.com/coq/coq/issues/6030).
* The behavior of `Program` is tweaked: `Unset Transparent Obligations`,
  `Obligation Tactic := idtac`, `Add Search Blacklist "_obligation_"`.  See
  [`base.v`](theories/base.v) for further details.
* It blocks `simpl` on all operations involving integers `Z` (by setting
  `Arguments op : simpl never`). We do this because `simpl` tends to expose
  the internals of said operations (e.g. try `simpl` on `Z.of_nat (S n) + y`).
  As a consequence of blocking `simpl`, due to
  [Coq bug #5039](https://github.com/coq/coq/issues/5039) the `omega` tactic
  becomes unreliable. We do not consider this an issue since we use `lia` (for
  which the aforementioned Coq bug was fixed) instead of `omega` everywhere.

## Prerequisites

This version is known to compile with:

 - Coq version 8.12.2 / 8.13.2 / 8.14.1 / 8.15.2 / 8.16.0

## Installing via opam

To obtain the latest stable release via opam (2.0.0 or newer), you have to add
the Coq opam repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

Then you can do `opam install coq-stdpp`.

To obtain a development version, add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

## Building from source

Run `make -jN` in this directory to build the library, where `N` is the number
of your CPU cores.  Then run `make install` to install the library.

## Unstable libraries

The `stdpp_unstable` folder contains a set of libraries that are not
deemed stable enough to be included in the main std++ library. These
libraries are available via the `coq-stdpp-unstable` opam package. For
each library, there is a corresponding "tracking issue" in the std++
issue tracker (also linked from the library itself) which tracks the
work that still needs to be done before moving the library to std++.
No stability guarantees whatsoever are made for this package.

Note that the unstable package is not released, so it only exists in the
development version of std++.

## Contributing to std++

If you want to report a bug, please use the
[issue tracker](https://gitlab.mpi-sws.org/iris/stdpp/issues).  You will have to
create an account at the
[MPI-SWS GitLab](https://gitlab.mpi-sws.org/users/sign_in) (use the "Register"
tab).

To contribute code, please send your MPI-SWS GitLab username to
[Ralf Jung](https://gitlab.mpi-sws.org/jung) to enable personal projects for
your account.  Then you can fork the
[Coq-std++ git repository](https://gitlab.mpi-sws.org/iris/stdpp), make your
changes in your fork, and create a merge request.

## Common problems

On Windows, differences in line endings may cause tests to fail. This can be 
fixed by setting Git's autocrlf option to true:

    git config --global core.autocrlf true
# stdpp_MC
