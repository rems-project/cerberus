# Onboarding Developer Guide to CN

This is a work-in-progress document to guide new developers to the CN codebase.
Of course, the best way to get to grips with the code is to pick a [starter
issue](https://github.com/orgs/GaloisInc/projects/23/views/9?filterQuery=label%3Acn+is%3Aopen+expertise%3Aonboarding),
perhaps request a pair-programming time to get started with it, and get stuck
in. However, this document should provide a conceptual structure on which to
hang the details as one fills them in. The below list of recordings of
walkthroughs and pair-programming sessions may also be helpful.

* [(video) 18/06/2024: Walkthrough with Q&A](https://drive.google.com/file/d/15aoDeTGtcx_JbESEli6aICcSC5eo8fEV/view?usp=sharing)

**NOTE: There is ongoing work to split CN out of the cerberus code base, at
which point much of the information in this document will need to be updated.**
For now, note the Cerberus acts as a "frontend" to CN, turning unruly C into a
relatively straightforward first-order functional programming langauge. CN
annotations of the form `/*@ ... @*/` are also handled by Cerberus ([see
below](#cn-pipeline-entry)).

## Example Commits for Different Features

* [CN VIP: Add split_case](https://github.com/rems-project/cerberus/commit/67e60e701fefbcfb6c581a6c18eb2355a277afc4)
* [CN Bitvectors: Update EachI construct w/ type annot](https://github.com/rems-project/cerberus/commit/79ddfa37fd199a147e6f4f55e2d5b73cea6b9d83)
* [CN VIP: Add index term for CopyAllocId](https://github.com/rems-project/cerberus/commit/4081026bd0e9a27ad536e31713766cb275242d73)
* [CN: Improve error message for CN statements](https://github.com/rems-project/cerberus/commit/39cbf5ccd9aced4c6eef9cbc9dfecd0bcd6c7eb9)

## Submitting PRs

General principles:

* [Fork the repo and keep it up to date.](https://github.com/rems-project/cerberus/blob/master/backend/cn/CONTRIBUTING.md#fork-the-repo)
* [Open PRs (even in draft state) to keep the build and CI is working.](https://github.com/rems-project/cerberus/blob/master/backend/cn/CONTRIBUTING.md#create-a-pr-and-get-it-reviewed)
* Make commits atomic (if it has an "and", usually split it up).
* Make PRs logically coherent (refactoring vs new features separate).
* As much as possible, break-up features to be reviewed piecemeal.
* Gate big features behind a flag.

## Pipeline

* Tokens: `parsers/c/tokens.ml`
* Lexer: `parsers/c/c_lexer.mll` (may change soon)
* Parser: `parsers/c/c_parser.mly` (ask about error messages!)
* Cabs: stands for "C Abstract Syntax". `fronted/model/cn.lem` is the relevant
  part (will change soon).
* Cabs to Ail: `frontend/model/cabs_to_ail.lem`. Also referred to as "desugaring".
* Ail: intermediate language (based on Clang). `frontend/model/ail/*`.
* Ail to Core: `frontend/model/translation.lem`.
* Core adjustments: if you run CN with `-d N` for `N = {1,2,3}` then it will
  produce `/tmp/0__original.core`, `/tmp/1__without_unspec.core`,
  `/tmp/2__after_peval.core`, `/tmp/3__mucore.mucore`. Some of these are referred to as 'milicore'.
* Core to mucore: `backend/cn/core_to_mucore.ml`
* Mucore: This is the thing that CN typechecks.

### CN Pipeline Entry

There are four types of CN parsing constructs (`parsers/c/c_parser.mly`), each
with a different entry point from which a parser can be started:
- cn\_statement: for proof guidance, debugging
- function\_spec: pre and post conditions
- loop\_spec: loop invariants
- cn\_toplevel: for declarations

1. C program is parsed into a C abstract sytnax tree (Cabs)
2. Toplevel magic comments are turned into CN toplevel declarations (`parser/c/c_parser_driver.ml`).
3. Magic statements, function specifications and loop specifications are
  inserted as string annotations (attributes).
4. Cabs is desugared, then elaborated into Core (including the CN toplevel declarations).
5. Core is turned into mucore, during which process the remaining magic
  comments are parsed and desugared into mucore as well (`backend/cn/parse.ml`).

## Key Files

* Entry point to the executable: `backend/cn/main.ml`
* Specification well-formedness checking: `backend/cn/wellTyped.ml`
* Actual C code type checking: `backend/cn/check.ml`
* Type checking mondad: `backend/cn/typing.ml{i}`
* SMT solver interface: `backend/cn/solver.ml`
* CN errors: `backend/cn/typeErrors.ml`
* HTML report generation: `backend/cn/report.ml`

## Key Types

* Basetypes: `backend/cn/baseTypes.ml`
* Terms: `backend/cn/terms.ml`
* Logical Argument Types: `backend/cn/logicalArgumentTypes.ml`
    ```
    let x = 5 + 5;      // Define
    take X = Pred(..);  // Resource
    assert (expr);      // Constraint
    ```
* Resource Types: the "signatures" of predicates, in `backend/cn/resourceTypes.ml`
* Resource Predicates: the defintion of predicates, in `backend/cn/resourcePredicates.ml`

## Code Cleanup

## Adding \*.mli files

You can generate them using the below **from the root of the repo** and **on a working build**:
``` 
[ ! -d backend/cn ] && echo "DO NOT PROCEED: Go to cerberus repo root" 
make && make install && make install_cn
opam install ocaml-print-intf
dune exec -- ocaml-print-intf backend/cn/XXXXX.ml | sed 's/Dune__exe.//g' > XXXXX.mli
# edit it
make && make install && make install_cn
```

* If you see something like
  ```
  module SymSet :
    sig
     ... enormous amount of stuff
    end
  ```
  replace it with something like the below (see `backend/cn/setup.mli`).
  ```
  module StringSet : Set.S with type elt = string
  ```
* Go through the .mli file and try to remove as many declarations as
  possible.
* Add a header, if you have enough information to write one.
  Headers look like this:
  ```
  (* Module Locations -- Utility functions for Cerberus locations
 
     This module adds a number of useful functions on locations to the
     ones already provided by Cerberus. *)
  ```
  If not, add a comment noting that it needs a header.  Comments
  should look like this:
  ```
     (* TODO: BCP: Describe what's needed... *)
  ```
* Open a PR and ask for reviews for anything you think needs a look from others.
  This way they will be notified via GitHub.

## Dependency graph

```
opam install codept
codept backend/cn/*.ml > cn-modules.dot
dot -Tpdf -o cn-modules.pdf # -x optionally to "simplify"
```

### Pending 

* Polishing pp.mli

