# Onboarding Developer Guide to CN

This is a work-in-progress document to guide new developers to the CN codebase.
Of course, the best way to get to grips with the code is to pick a [starter
issue](https://github.com/orgs/GaloisInc/projects/23/views/9?filterQuery=label%3Acn+is%3Aopen+expertise%3Aonboarding),
perhaps request a pair-programming time to get started with it, and get stuck
in. However, this document should provide a conceptual structure on which to
hang the details as one fills them in.

* [(video) 18/06/2024: Walkthrough with Q&A](https://drive.google.com/file/d/15aoDeTGtcx_JbESEli6aICcSC5eo8fEV/view?usp=sharing)

## Submitting PRs

General principles:

* Make commits atomic (if it has an "and", probably split it up).
* Make PRs logically coherent (refactoring vs new features separate).
* Keep the build and CI working.
* Rebase on master frequently (daily: `git pull --rebase master`).
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

### Some external Cerberus modules

[Some notes from Christopher's tour of CN on parts of Cerberus that CN
depends on...]

These bits are not part of CN – this is the Cerberus C semantics – but
important as background and context.  CN uses Cerberus to translate
C/CN to Core.

frontend/model/core.lem
* Lem is “sort of OCaml” but can also export to theorem provers
* `funs` is the map of all the functions in scope
* Body of a function is a “generic_expr_”
* Grammar of expressions: generic_expr
* Stack local variable in C program: generic_action_
* Core is general, while mucore (part of CN) is more specific

cabs.lem
* The first level of abstract syntax
* frontend/model/ail/ailSyntax.lem
* Clarifies some issues with scoping, structs, for loops get turned into while loops
* Still distinguishes statements and expressions
* This then gets turned into Core

### Entry Points:

There are four types of CN parsing constructs, each with
a different entry point from which a parser can be started:
     - cn_statement: for proof guidance, debugging
     - function_spec: pre and post conditions
     - loop_spec: loop invariants
     - cn_toplevel: for declarations

1. C program is parsed into a C abstract sytnax tree (Cabs)
2. Toplevel magic comments are turned into CN toplevel declarations.
3. Magic statements, function specifications and loop specifications are
  inserted as string annotations (attributes).
4. Cabs is desugared, then elaborated into Core (including the CN toplevel declarations).
5. Core is turned into mucore, during which process the remaining magic
  comments are parsed and desugared into mucore as well. *)

### Example commits
* [CN VIP: Add split_case](https://github.com/rems-project/cerberus/commit/67e60e701fefbcfb6c581a6c18eb2355a277afc4)
* [CN Bitvectors: Update EachI construct w/ type annot](https://github.com/rems-project/cerberus/commit/79ddfa37fd199a147e6f4f55e2d5b73cea6b9d83)
* [CN VIP: Add index term for CopyAllocId](https://github.com/rems-project/cerberus/commit/4081026bd0e9a27ad536e31713766cb275242d73)

## Key types

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

## Dependency Graph

```
opam install codept
codept backend/cn/*.ml > cn-modules.dot
dot -Tpdf -o cn-modules.pdf # -x optionally to "simplify"
```

## Useful recipies

### To add a .mli file for a given .ml file

`cd backend/cn`

`(cd ../..; dune exec -- ocaml-print-intf backend/cn/XXXXX.ml) > XXXXX.mli`

inspect XXXXX.mli to make sure that it looks semi-reasonable

`make -C ../.. cn`

inspect XXXXX.mli more closely

  - remove instances of `Dune__exe.`

  - if you see something like

       module SymSet :
         sig
           ... enormous amount of stuff

    replace it with

       module SymSet = Set.Make(Sym)

    You may need to add a bit more information to help typechecking --
    e.g., in setup.mli we have

       module StringSet : Set.S with type elt = string

  - Go through the .mli file and try to remove as many declarations as
    possible

  - Add a header, if you have enough information to write one.
    Headers look like this:

       (* Module Locations -- Utility functions for Cerberus locations

          This module adds a number of useful functions on locations to the
          ones already provided by Cerberus. *)

    If not, add a comment noting that it needs a header.  Comments
    should look like this:

       (* TODO: BCP: Describe what's needed... *)

  - Leave comments about anything else that needs a look from others

  - Recompile again to make sure nothing is broken

# Things to do

## Information that would be useful to add, generally

Some useful high-level information we could add (e.g. to this file :-)...

   - Where is the parser?  How does it connect to the rest?
   - What is the relation between the Cerberus and CN codebases?
   - What are the main starting points in this directory?
   - If I want an overview of the code, in what order should I look at
     things?
   - What are the most important top-level modules, and what is the
     overall flow of information between them?
   - "If I want to add <common sort of thing to add>, where do I look?"

## Small pending tasks

- More polishing on pp.mli

- incorporate the comments from
https://docs.google.com/document/d/1AVRjj9dWcfOskDe_Fmdwu2pfARcQ985sgW3LR6gVtXY/edit

- change all filenames to snake_case
