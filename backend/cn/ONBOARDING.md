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
