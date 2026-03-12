# Cerberus

Cerberus is a C semantics tool written in OCaml with a Dune build system.

## Build & run

```sh
dune build                        # build everything
dune build backend/driver/        # build the cerberus binary only
./_build/default/backend/driver/cerberus --help

# Common invocations
cerberus file.c                   # parse + elaborate only
cerberus --exec --batch file.c    # execute and print result
cerberus --pp core file.c         # pretty-print Core IR
cerberus --typecheck-core file.c  # typecheck the Core IR
cerberus --sw mem2reg file.c      # enable a switch
```

## Architecture

| Library / binary | Path | Role |
|---|---|---|
| `cerb_frontend` | `ocaml_frontend/` | C→AIL→Core elaboration, rewriters, switches |
| `cerb_backend` | `backend/common/` | Pipeline orchestration (`pipeline.ml`) |
| `cerberus` binary | `backend/driver/main.ml` | CLI entry point |

The pipeline in `backend/common/pipeline.ml`:
1. C source → Cabs (C parser)
2. Cabs → AIL (`Cabs_to_ail.desugar`)
3. AIL → Core (`Translation.translate`)
4. `core_passes` — per-file Core transforms, then typechecking

## Important: generated code

`ocaml_frontend/generated/` is auto-generated from Lem specs in
`frontend/model/`. **Do not edit those files directly.** Read them only to
understand translation output; the authoritative sources are the `.lem` files.

The `ocaml_frontend/dune` file uses `(include_subdirs unqualified)`, so any
`.ml` file added anywhere under `ocaml_frontend/` (including subdirs) is
automatically compiled into `cerb_frontend`.

## How to add a Cerberus switch

1. Add a constructor to `cerb_switch` in `ocaml_frontend/switches.ml` and
   `ocaml_frontend/switches.mli`.
2. Add a `| "name" -> Some SW_name` case in `read_switch` (before `| _ -> None`).
3. For a simple boolean switch, add `| SW_name` to the equality arm of `pred`
   (lines ~115–126 of `switches.ml`).

## How to add a Core pass

1. Create `ocaml_frontend/rewriters/my_pass.ml` — see `remove_unspecs.ml` for
   a minimal example. Expose `val transform_file`.
2. In `backend/common/pipeline.ml`, inside `core_passes`, add after the
   `Remove_unspecs` block:
   ```ocaml
   let core_file =
     if Switches.(has_switch SW_my_pass) then
       My_pass.transform_file core_file
     else core_file in
   ```

## Buidling

Always use `make && make install` for building instead of dune commands.

## Tests

```sh
cd tests
USE_OPAM='' bash run.sh              # full suite (parsing, ci, tcc, gcc-torture)
USE_OPAM='' bash run-ci.sh           # CI subset only
```

Always set `USE_OPAM=''`; without it, `common.sh` invokes cerberus via
`dune exec`, which emits deprecation warnings and timing lines on stderr that
pollute output comparisons for `*.error.c` and `*.syntax-only.c` tests.

CI tests live in `tests/ci/`. Each test is a `.c` file run with
`cerberus --exec --batch`; expected output is in `tests/ci/expected/*.expected`.
Instructions to Claude for writing OCaml code: 

# Writing Code

0. When writing code, do these things first: 

   1. Write a plan with high-level architectural decisions. Analyze this plan for defects, 
      and keep fixing them until no obvious deficiencies remain. 

   2. Write a detailed design document, with design choices for each module. Again, before
      proceeding to implementaiton, analyze the design for obvious flaws before proceeding. 
      If there is a fundamental design problem, DO NOT try to smooth it over. Instead, consult
      the user about how to proceed, giving them the key options. 

   3. If the detailed design reveals a key flaw, consider whether the high-level plan needs
      to be revised. Consult the user about how to proceed, and give them some options. 

   4. Copy each design document to a file `doc/history/YYYY-MM-DD_PLAN-NAME.md`, so the user can
      read it, and new sessions can understand the changes. 

# Writing OCaml code specifically

1. Programs should be composed of small modules, each implementing a single concern or
   data structure. However, mutual recursion between functions is a good reason to
   place them in the same module — prefer a single larger module with `and`-linked
   mutually recursive functions over separate modules connected by callbacks or
   recursive module declarations.

2. Write .mli files first, before writing any part of a module.

   - .mli files should emphasize the algebraic structure of the data structure. 

   - Name the primary type of an .mli file as `t`, so that clients can refer to it as 
     `Foo.t`, or `'a Foo.t`. 

   - Unless otherwise necessary, hide the implementation type. 

   - Parameterized types of the form `'a t` should expose a `map : ('a -> 'b) -> 'a t -> 'b t`
     primitive in their interface. 

   - If a type constructor has monadic structure, then define `return : 'a -> 'a t` and
     `(let+) : 'a -> ('a -> 'b t) -> 'b t` operations.

   - If a type can be ordered, then expose a `compare : t -> t > int` primitive. 

   - If a type can be printed, expose a `print : Format.formatter -> t -> unit` method in the 
     interface. Use the Format module's indentation directives to ensure that print methods are
     nicely laid out.

   - If a module exposes a parameterized type, give parameterized comparison and printing
     functions. 

3. Here are some bad language features to avoid: 

   - NEVER use Obj.magic, or any other feature which can break type safety. 

   - NEVER use generic equality, since this violates data abstraction. Always use a 
     type-specific `compare` operation.

3. Unless explicitly instructed otherwise, DO NOT write code which uses effects.

   - Use a monad with a result type instead of exceptions. 

   - Prefer monadic state-passing to mutable data structures. 

   - Permission to use mutable data structures is granted on a per-module basis, and 
     permission in one module does not grant it in any other. 

   - Do not perform IO operations, except for debugging, and in any top-level main-like functions. 

3. Write programs by pattern matching over data structures. Avoid
   using partial accessors or incomplete patterns matches.
  
4. Higher-order functions should be used sparingly, in idiomatic ways.

   - Introducing monadic code to eliminate repeated nested pattern matches is acceptable. 
   - Use of map, filter, and other algebraically well-behaved functions is acceptable. 
   - Avoid the use of folds, because they offer no reasoning advantages over explicit
     structural recursion.
