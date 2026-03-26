# Copy-Propagation: Pattern-Aware Analysis

**Date:** 2026-03-27
**Branch:** mem2reg
**Status:** Plan (pre-implementation)

---

## Problem Statement

The current `copy_propagation.ml` decides whether to replace a tail expression with
`unit` based solely on the expression's shape (`can_prop_and_rm`), without consulting
the pattern the value will be bound to. This produces type-incoherent output.

### Concrete Bug

Consider elaborated Core like:

```core
let Specified(x) = pure(Specified(ptr)) in body
```

Here `ptr` is a propagatable sym (no local binders). The current two-phase flow is:

1. **`split_tuple`** sees `PEctor(Cspecified, [PEsym ptr])`.
   Not a `Ctuple`, so falls to `prop_and_rm`.
   `can_prop_and_rm` returns `true` (all sub-expressions are free of local binders).
   Replaces expression with `PEval Vunit`. Returns `Leaf(Some PEctor(Cspecified, [PEsym ptr]))`.

2. **`match_pat_tree`** sees pattern `CaseCtor(Cspecified, [CaseBase(Some x, _)])` vs
   `Leaf(Some …)`.
   The only `Leaf` arms handle `CaseBase(Some s, _)` and `CaseBase(None, _)`.
   Falls to `_ -> ([], pat)` — no bindings extracted, original pattern kept.

3. **Net result:**
   - Expression has already been rewritten to `unit`.
   - Pattern is still `Cspecified(x)`.
   - Output: `let Cspecified(x) = pure(unit) in body` — **type error**.
   - `x` is **not** substituted for `ptr` in `body`.

The same kind of mismatch can arise for any `CaseCtor` that wraps propagatable content
but is not a `Ctuple`.

---

## High-Level Plan

Replace the existing two-phase (build `pexpr_tree` + `match_pat_tree`) approach with a
**single-pass pattern-aware analysis**. The analysis takes both the binding pattern and
the expression/pexpr simultaneously, and returns a coherent triple:

```
(bindings : (sym * pexpr) list, new_pat : pattern, new_pe/e : …)
```

where `new_pe` and `new_pat` are guaranteed to be type-compatible with each other.

The `pexpr_tree` type and its associated build/match functions (`split_tuple`,
`prop_and_rm`, `eventually_pure`, `tail_pexpr`, `match_pat_tree`) are **removed**.
Two new functions replace them:

| New function | Replaces |
|---|---|
| `analyze_pat_pexpr` | `split_tuple` + `match_pat_tree` (pure case) |
| `analyze_pat_expr`  | `eventually_pure`/`tail_pexpr` + `match_pat_tree` (effectful case) |

Call sites (`Ewseq`, `Esseq`, `Elet` in `propagate_expr`; `PElet` in `propagate_pexpr`)
switch to using the new functions.

### Architectural defect analysis

| Concern | Assessment |
|---|---|
| Backwards compatibility of pattern rewriting | Safe: the `CaseBase` cases are preserved exactly as before. The only new behaviour is for previously-missed `CaseCtor` patterns. |
| Arity mismatch between `Ctuple` pat and `PEctor(Ctuple, pes)` | Defensive: if lengths differ, fall through to the conservative `([], pat, pe)` case. |
| `Eunseq` arity mismatch with tuple pattern | Same: fall through to conservative. |
| `can_prop_and_rm binders` correctness inside nested patterns | The `binders` list is passed down through `analyze_pat_expr` as we cross sequential binders, preserving the invariant from the original code. |
| Type annotation on residual `CaseBase` | When replacing a `CaseBase(Some s, bty)` or `CaseBase(None, bty)` with a wildcard, we use `BTy_unit` for the residual as before. When wrapping in `Cspecified`, we keep the inner residual type. |

No fundamental architectural problem identified.

---

## Detailed Design

### 1. Keep: `can_prop_and_rm`

No changes. Signature and semantics unchanged:

```ocaml
val can_prop_and_rm : Symbol.sym list -> pexpr -> bool
```

Returns `true` iff the pexpr has no free occurrences of the given locally-bound syms and
is safe to hoist.

### 2. Keep: `binders_of_pat`

No changes.

### 3. Remove

- `pexpr_tree` type
- `prop_and_rm`
- `split_tuple`
- `eventually_pure`
- `tail_pexpr`
- `match_pat_tree`

### 4. New: `analyze_pat_pexpr`

```ocaml
val analyze_pat_pexpr
  :  Symbol.sym list      (* locally-bound syms, must not escape *)
  -> pattern              (* binding pattern *)
  -> pexpr                (* RHS pure expression *)
  -> (Symbol.sym * pexpr) list * pattern * pexpr
  (* (bindings, new_pat, new_pe) *)
```

Cases:

```
CaseBase(Some s, _),  pe   when can_prop_and_rm binders pe
  → ([(s, pe)], CaseBase(None, BTy_unit), PEval Vunit)

CaseBase(None, _),    pe   when can_prop_and_rm binders pe
  → ([],        CaseBase(None, BTy_unit), PEval Vunit)

CaseBase(_, _),       pe   (* not propagatable *)
  → ([],        pat,                     pe)

CaseCtor(Ctuple, pats), PEctor(Ctuple, pes)   (* same arity *)
  → recurse element-wise via List.map2 analyze_pat_pexpr
    combine bindings; rebuild Ctuple pat and expr

CaseCtor(Cspecified, [inner_pat]), PEctor(Cspecified, [inner_pe])
  → (bindings', CaseCtor(Cspecified, [new_inner_pat]),
                PEctor(Cspecified, [new_inner_pe]))
    where (bindings', new_inner_pat, new_inner_pe) =
      analyze_pat_pexpr binders inner_pat inner_pe

(* Conservative fallthrough *)
_, _
  → ([], pat, pe)
```

**Design note:** `Cunspecified` (`PEctor(Cunspecified, [])`) carries no sub-expressions
to propagate, so the conservative fallthrough handles it correctly with no special case
needed. `Cnil` and other ctors similarly fall through.

### 5. New: `analyze_pat_expr`

```ocaml
val analyze_pat_expr
  :  Symbol.sym list      (* locally-bound syms *)
  -> pattern              (* the *outer* binding pattern, not the inner chain pats *)
  -> expr
  -> (Symbol.sym * pexpr) list * pattern * expr
```

This descends through sequential chains (`Esseq`, `Ewseq`, `Elet`, `Ebound`, `Eannot`)
to find the tail, then delegates to `analyze_pat_pexpr` for the pure case.

```
Epure pe
  → let (bs, new_pat, new_pe) = analyze_pat_pexpr binders pat pe in
    (bs, new_pat, Epure new_pe)

Eunseq es
  → match pat with
    | CaseCtor(Ctuple, pats) when List.length pats = List.length es →
        recurse element-wise: analyze_pat_expr binders pats_i es_i
        combine; rebuild Ctuple pat and Eunseq
    | _ → conservative: ([], pat, expr)

Ewseq(inner_pat, e1, e2)
  → let binders' = binders_of_pat inner_pat @ binders in
    let (bs, new_outer_pat, new_e2) = analyze_pat_expr binders' pat e2 in
    (bs, new_outer_pat, Ewseq(inner_pat, e1, new_e2))
    (* Note: inner_pat / e1 are NOT rewritten here — that is the job of
       propagate_expr when it processes e1 as its own binding site *)

Esseq(inner_pat, e1, e2)
  → analogous to Ewseq

Elet(inner_pat, pe1, e2)
  → let binders' = binders_of_pat inner_pat @ binders in
    let (bs, new_outer_pat, new_e2) = analyze_pat_expr binders' pat e2 in
    (bs, new_outer_pat, Elet(inner_pat, pe1, new_e2))

Ebound e
  → let (bs, new_pat, new_e) = analyze_pat_expr binders pat e in
    (bs, new_pat, Ebound new_e)

Eannot(al, e)
  → analogous to Ebound

(* Conservative fallthrough for Eif, Ecase, Eccall, Eaction, … *)
_
  → ([], pat, expr)
```

**Critical invariant:** `analyze_pat_expr` only rewrites the *tail* of the chain (the
`e2` in Esseq/Ewseq/Elet, or the final `Epure`). It does **not** rewrite `e1` — that is
propagated separately by `propagate_expr`'s own recursive call.

### 6. Updated call sites in `propagate_expr`

```ocaml
| Ewseq (pat, e1, body) ->
    let e1' = propagate_expr env e1 in
    let (bindings, new_pat, e1'') = analyze_pat_expr [] pat e1' in
    let env' = extend_env_list env bindings in
    Expr (annots, Ewseq (new_pat, e1'', propagate_expr env' body))

| Esseq (pat, e1, body) ->
    (* analogous *)

| Elet (pat, pe1, body) ->
    let pe1' = propagate_pexpr env pe1 in
    let (bindings, new_pat, pe1'') = analyze_pat_pexpr [] pat pe1' in
    let env' = extend_env_list env bindings in
    Expr (annots, Elet (new_pat, pe1'', propagate_expr env' body))
```

And in `propagate_pexpr` for `PElet`:

```ocaml
| PElet (pat, pe1, pe2) ->
    let pe1' = propagate_pexpr env pe1 in
    let (bindings, new_pat, pe1'') = analyze_pat_pexpr [] pat pe1' in
    let env' = extend_env_list env bindings in
    Pexpr (annots, bty, PElet (new_pat, pe1'', propagate_pexpr env' pe2))
```

### 7. Detailed design defect analysis

| Concern | Assessment |
|---|---|
| `analyze_pat_expr` rewrites the tail expr (inner chain) but not `e1` | Correct by design: `e1` is the action / other expression being sequenced; its tail is what `body` is bound to. Only the tail pure value can be extracted. The `propagate_expr` call on `e1` handles its own internals. |
| Binders passed as `[]` to `analyze_pat_expr` at call sites | Safe: `analyze_pat_expr` re-accumulates binders as it descends through the chain. The outer call always starts fresh. |
| `Eunseq` within `analyze_pat_expr` — does it arise in practice? | Yes: `Ewseq(tuple_pat, Eunseq([e1;e2]), body)` is generated by the elaboration of parallel operations. The handling mirrors the existing `Node` case. |
| Propagating `PEsym` inside `Cspecified` wrapper — annotations preserved? | Yes: destructure `Pexpr(outer_annots, outer_bty, PEctor(Cspecified, [inner_pe]))` and reuse `outer_annots`/`outer_bty` in the rebuilt node. |
| `analyze_pat_expr` for Esseq/Ewseq: `inner_pat` is NOT rewritten | Correct: rewriting `inner_pat` would affect the binding between `e1` and `e2`, which is separate from the outer binding between the whole Esseq and `body`. |

### 8. Annotation preservation for reconstructed `PEctor`

In `analyze_pat_pexpr`, when handling `CaseCtor(Cspecified, [inner_pat])` vs
`PEctor(Cspecified, [inner_pe])`, we reconstruct the outer `PEctor`. We must preserve
the `Pexpr(outer_annots, outer_bty, …)` wrapper. The cleanest way: destructure the
incoming `pexpr` as `Pexpr(outer_annots, outer_bty, PEctor(Cspecified, [inner_pe]))` in
the match arm, and use `outer_annots`/`outer_bty` for the reconstruction.

Similarly for `Ctuple`: destructure and reuse `outer_annots`/`outer_bty` from the
original pexpr.

No fundamental flaw — just a detail to attend to in implementation.

---

## Summary of Changes

| File | Change |
|---|---|
| `ocaml_frontend/rewriters/copy_propagation.ml` | Remove `pexpr_tree`, `prop_and_rm`, `split_tuple`, `eventually_pure`, `tail_pexpr`, `match_pat_tree`; add `analyze_pat_pexpr`, `analyze_pat_expr`; update `propagate_expr` and `propagate_pexpr` call sites |

No other files change.

---

## Testing

The existing copy-prop test suite in `tests/` covers this change fully and should be run
after every build.

### Regression: Phase 1

```sh
cd tests
USE_OPAM='' bash run-copy-prop-phase1.sh
```

Runs all CI tests (`0001`–`0365` and newer) with `--sw copy_prop` and checks that
outputs match the committed `.expected` files. This guards against any change to the
pass that silently alters execution results.

The refactored code must pass Phase 1 with no new failures. Because the bug affected
only bindings with `CaseCtor` outer patterns (not `CaseBase`), most existing tests will
be unaffected; but the regression suite confirms nothing regressed.

### Elimination: Phase 2

```sh
cd tests
USE_OPAM='' bash run-copy-prop-phase2.sh
```

Checks that `--sw copy_prop` leaves the expected number of `create()` calls in the
pretty-printed Core IR for the dedicated copy-prop tests (`0366`–`0373`). Also runs the
`0373` integration test with both `--sw copy_prop --sw mem2reg`.

The expected `create()` counts in Phase 2 were set for the `CaseBase` propagation case.
If the fix causes additional propagation through `Cspecified` wrappers, the counts for
some tests may need to be updated — this is expected and correct behaviour.

### Full CI

```sh
cd tests
USE_OPAM='' bash run-ci.sh
```

Run the full CI subset after the phase scripts pass to confirm no wider regressions.

---

## Post-Implementation Addendum

*(To be filled after implementation, testing, and user feedback.)*
