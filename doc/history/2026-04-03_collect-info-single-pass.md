# Plan: Combine `collect_esave_defs` and `collect_creates` into one pass

## Context

`find_promotable` in `ocaml_frontend/rewriters/core_mem2reg.ml` currently calls two
separate full-body traversals:

1. `collect_esave_defs body` — walks the AST with a mutable `memo` ref to collect
   all `Esave` label → entry mappings (lines 167–189).
2. `collect_creates ~also_fun_args body` — recursive list-returning walk to collect
   `Create`-bound `ptr_sym` candidates (lines 274–302).

Both traverse exactly the same node set, so two passes are redundant. The task is to
merge them into a single `collect_info ~also_fun_args body` that uses mutable refs for
both outputs and returns them as a pair.

---

## High-level design

Replace the two functions with:

```ocaml
val collect_info
  :  also_fun_args:bool
  -> (unit, unit, Symbol.sym) generic_expr
  -> use list memo_save_info * Symbol.sym list
```

Internally it holds two mutable refs:
- `esave_memo : (Symbol.sym, _ esave_memo_entry) Pmap.map ref`  (same as `collect_esave_defs`)
- `creates    : Symbol.sym list ref`  (collected in reverse, reversed on return)

A single inner `walk` function merges the two traversals. The match order is:

1. **`Esave` arm** — populate `esave_memo`, recurse into `esave_body` (unchanged from
   `collect_esave_defs`; also subsumes `collect_creates`'s bare `Esave` arm).
2. **Create-binding `Esseq` arm (PrefSource | PrefCompoundLiteral)** — prepend
   `ptr_sym` to `creates`, `walk body` only (the `Eaction` RHS is a leaf).
3. **Create-binding `Esseq` arm (PrefFunArg) `when also_fun_args`** — same.
4. **Generic `Ewseq`/`Esseq` arm** — `walk e1; walk e2`.
5. All other structural arms unchanged from `collect_esave_defs`.

Return `(!esave_memo, List.rev !creates)`.

### Correctness notes

- The specific Create-`Esseq` arms shadow the generic `Esseq` arm, exactly as in
  `collect_creates`.
- For `PrefFunArg` when `also_fun_args = false`: the guard fails, so the expression
  falls through to the generic `Esseq` arm → `walk e1; walk e2`.  `e1` is
  `Eaction _` (a leaf), so the effect is just `walk body` — identical to
  `collect_creates`'s behaviour.
- `creates` is prepended and reversed to preserve left-to-right traversal order
  (matching `collect_creates`'s `List.concat_map` order).

---

## Files to modify

| File | Change |
|------|--------|
| `ocaml_frontend/rewriters/core_mem2reg.ml` | Replace `collect_esave_defs` (lines 165–189) and `collect_creates` (lines 268–302) with `collect_info`; update call site in `find_promotable` (lines 521, 525). |

---

## Detailed implementation

### New function (replaces both, placed at line 165)

```ocaml
(* collect_info: single pass over the function body that simultaneously
   (a) collects all Esave definitions into a memo table, and
   (b) finds Create-bound syms that are candidates for promotion.    *)
let collect_info ~also_fun_args body =
  let esave_memo = ref (Pmap.empty Symbol.compare_sym) in
  let creates    = ref [] in
  let rec walk (Expr (_, e_)) =
    match e_ with
    | Esave ((label_sym, _), params, esave_body) ->
        let entry = {
          params  = List.map (fun (s, (_, pe)) -> (s, pe)) params;
          body    = esave_body;
          results = ref (Pmap.empty Symbol.compare_sym);
        } in
        esave_memo := Pmap.add label_sym entry !esave_memo;
        walk esave_body
    | Esseq (
        Pattern (_, CaseBase (Some ptr_sym, _)),
        Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _,
            (Symbol.PrefSource _ | Symbol.PrefCompoundLiteral _)))))),
        body
      ) ->
        creates := ptr_sym :: !creates;
        walk body
    | Esseq (
        Pattern (_, CaseBase (Some ptr_sym, _)),
        Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefFunArg _))))),
        body
      ) when also_fun_args ->
        creates := ptr_sym :: !creates;
        walk body
    | Ewseq (_, e1, e2) | Esseq (_, e1, e2) -> walk e1; walk e2
    | Eif (_, e1, e2)                        -> walk e1; walk e2
    | Ecase (_, arms)   -> List.iter (fun (_, e) -> walk e) arms
    | Elet (_, _, e) | Ebound e | Eannot (_, e) -> walk e
    | Eunseq es | End es | Epar es           -> List.iter walk es
    | Epure _ | Eaction _ | Ememop _ | Eccall _ | Eproc _
    | Erun _ | Ewait _ | Eexcluded _        -> ()
  in
  walk body;
  (!esave_memo, List.rev !creates)
```

### Updated call site in `find_promotable` (lines 520–525)

Replace:
```ocaml
let use_memo  : use list memo_save_info = collect_esave_defs body in
let seq_memo  : seq_memo =
  Pmap.map (fun { params; body; _ } ->
    { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) use_memo in
let creates = collect_creates ~also_fun_args body in
```

With:
```ocaml
let (use_memo : use list memo_save_info), creates = collect_info ~also_fun_args body in
let seq_memo  : seq_memo =
  Pmap.map (fun { params; body; _ } ->
    { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) use_memo in
```

---

## History doc

Copy this plan to `doc/history/2026-04-03_collect-info-single-pass.md` before
implementation.

---

## Verification

```sh
make && make install
cd tests && USE_OPAM='' bash run-ci.sh
```

All CI tests should pass unchanged (pure refactor, no behavioural change).

---

## Post-implementation addendum

_To be filled in after implementation._
