
# mem2reg — value-passing calling convention support

**Date:** 2026-03-16
**Branch:** mem2reg
**Files changed:** `ocaml_frontend/rewriters/core_mem2reg.ml`, `ocaml_frontend/rewriters/core_mem2reg.mli`

## Context

The mem2reg analysis (`ocaml_frontend/rewriters/core_mem2reg.ml`) previously only
promoted `Create(PrefSource _)` bindings — C source-level local variables.
Function parameters were excluded because under the standard `Normal_callconv`
they are passed as pointers by the caller; the callee receives a pointer it does
not own, so there is no `Create` inside the callee to promote.

Under `Inner_arg_callconv` (enabled by `SW_inner_arg_temps`, used by CN), the
elaboration places the allocation, initialisation, and deallocation of each
non-variadic parameter **inside the callee body** as a `Create(PrefFunArg _)` /
`Store` / ... / `Kill` sequence.  These have exactly the same shape as a
promotable local variable, and should be promoted when the parameter's address
is never taken.

`file.calling_convention` (type `Core.calling_convention`, values
`Normal_callconv | Inner_arg_callconv`) is already threaded through the entire
pipeline.  The pass just needs to read it.

## Design

The minimal change is to add a single `~also_fun_args : bool` parameter to
`collect_creates`.  When `true`, the function also yields syms bound by
`Create(PrefFunArg _)` alongside the existing `Create(PrefSource _)` arm.
`transform_file` computes `also_fun_args` once from `file.calling_convention`
and threads it down.

This keeps the analysis path-insensitive to the calling convention: the
promotability predicate (`collect_uses`) is unchanged — it already handles any
Create-bound pointer sym the same way, regardless of whether it came from a
local variable or a parameter slot.

### Why `also_fun_args` rather than inspecting the prefix inside `collect_uses`

`collect_uses` classifies every **use** of a sym (load / store / kill / other).
Whether a sym was *introduced* by a `PrefSource` or `PrefFunArg` create is
orthogonal to how it is used.  Introducing the distinction at the
`collect_creates` level (where the sym is bound) keeps both functions
single-purpose.

## Changes

### `collect_creates` — new `~also_fun_args` arm

```ocaml
(* collect_creates finds Create-bound syms that are candidates for
   promotion.  Under Normal_callconv only PrefSource (C local variables)
   are considered; under Inner_arg_callconv PrefFunArg (callee-owned
   parameter temporaries) are also included, since in that convention
   the callee creates and owns the argument slot.                      *)

let rec collect_creates ~also_fun_args (Expr (_, e_)) : Symbol.sym list =
  match e_ with
  | Esseq (
      Pattern (_, CaseBase (Some ptr_sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefSource _))))),
      body
    ) ->
      ptr_sym :: collect_creates ~also_fun_args body
  | Esseq (
      Pattern (_, CaseBase (Some ptr_sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefFunArg _))))),
      body
    ) when also_fun_args ->
      ptr_sym :: collect_creates ~also_fun_args body
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      collect_creates ~also_fun_args e1 @ collect_creates ~also_fun_args e2
  (* remaining arms all thread ~also_fun_args *)
```

### `transform_file` — read `file.calling_convention`

```ocaml
let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  List.iter (fun (f_sym, decl) ->
    match decl with
    | Proc (_, _, _, _, body) ->
        ignore (find_promotable ~also_fun_args f_sym body)
    | Fun _ | ProcDecl _ | BuiltinDecl _ -> ()
  ) (Pmap.bindings_list file.funs);
  file
```

### `.mli` doc comment

```ocaml
(** Promote function-local, non-address-taken C variables — and, under
    [Inner_arg_callconv], callee-owned parameter temporaries — from
    Create/Store0/Load0/Kill sequences to pure Core let-bindings.
    Which categories are considered is determined by
    [file.calling_convention]. *)
```

## Calling-convention background

Under `Normal_callconv` (the default), function arguments are passed as
pointers; the **caller** allocates the argument slot.  The callee only holds a
borrowed pointer and never owns the allocation, so there is no matching
`Create`/`Kill` in the callee body.

Under `Inner_arg_callconv` (switch `SW_inner_arg_temps`, used by CN), arguments
are passed as Core **values** (`BTy_loaded _`); the **callee** allocates the
argument slot via `Create(PrefFunArg _)` at function entry, initialises it with
a `Store`, and deallocates it with `Kill` on every exit path.  The resulting
shape is identical to a C local variable and is directly promotable if the
parameter's address is never taken.

## Verification

```sh
make && make install

# 1. Normal_callconv: CI suite unaffected
cd tests && USE_OPAM='' bash run-ci.sh   # 198/198

# 2. Inner_arg_callconv: parameter slot promoted
cerberus --sw="mem2reg,inner_arg_temps" -d 3 \
  tests/ci/0347-mem2reg_no_promote_arg.c 2>&1 | grep "\[mem2reg\]"
# id: 1 promotable: [x]   ← parameter x now promoted
# main: 1 promotable: [x]

# 3. Address-taken local: not promoted even under Inner_arg_callconv
cerberus --sw="mem2reg,inner_arg_temps" -d 3 \
  tests/ci/0346-mem2reg_no_promote_address.c 2>&1 | grep "\[mem2reg\]"
# foo: 1 promotable: [p]   ← p slot (never address-taken in foo) promoted
# main: 0 promotable: []   ← x address taken via &x, not promoted
```
