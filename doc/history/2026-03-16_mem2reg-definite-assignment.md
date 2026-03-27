# Plan: mem2reg — Definite-Assignment Analysis Fix (revised)

## Problem

The current `find_promotable` checks that every use of a Create-bound symbol is
a Load0, Store0, or Kill.  However it does **not** verify that a Load0 is always
preceded by a Store0 on every path through the function body.

If a promotable variable is loaded before it has been stored on some path, the
Create node will be dropped and there will be no `Elet` binding that introduces the
loaded value's name.  The transformed program is ill-scoped even if the original C
was undefined behaviour.

## Polarity system

`frontend/model/core.lem` lines 152-154:

```lem
type polarity =  (* memory action polarities *)
 | Pos (* sequenced by letweak and letstrong *)
 | Neg (* only sequenced by letstrong *)
```

`Ewseq` is `letweak`; `Esseq` is `letstrong`.  **`Neg` actions in e1 of an
`Ewseq` are not sequenced before e2.**  Every `Store0` in generated code is
wrapped in `Paction(Neg, ...)` and placed in the e1 of an `Ewseq`, so a Store0
in e1 of an `Ewseq` is NOT guaranteed visible to e2.

## New predicate: `check_definitely_init`

Add a recursive helper that returns a pair:

```ocaml
(* Returns (safe, init_after):
     safe       – no load-before-store on any syntactic path through expr
     init_after – on ALL syntactic paths through expr, at least one store
                  has occurred (so a subsequent load would be safe)       *)
val check_definitely_init
  :  Symbol.sym     (* the pointer symbol being analysed *)
  -> bool           (* already_init: a store has occurred on every path so far *)
  -> (unit, unit) Core.generic_expr
  -> bool * bool
```

### Recursive rules

Starting call: `check_definitely_init sym false body`
(the variable is uninitialized at the point of its `Create`).

| Node | `safe` | `init_after` |
|---|---|---|
| `Store0(ptr_sym, …)` | `true` | `true` |
| `Load0(…, ptr_sym, …)` | `already_init` | `already_init` |
| `Kill(…, ptr_sym)` | `true` | `false` (scope ends) |
| `SeqRMW(_, _, PEsym ptr_sym, …)` | `already_init` | `true` |
| `Esseq(_, e1, e2)` | run e1 → `(s1, ia1)`, run e2 with `ia1` → `(s2, ia2)`; `s1 && s2` | `ia2` |
| `Ewseq(_, e1, e2)` | run e1 → `(s1, ia1)`, run e2 with **`already_init`** → `(s2, ia2)`; `s1 && s2` | `ia1 \|\| ia2` |
| `Eunseq(arms)` | run each arm with `already_init`; `AND(si)` | `AND(iai)` |
| `Eif(_, et, ef)` | run et and ef both with `already_init`; AND safes | AND `init_after`s |
| `Ecase(_, arms)` | run every arm with `already_init`; AND all `safe` | AND all `init_after` |
| `Esave(…)` | conservative: if sym occurs anywhere inside → `false`; else `true` | `already_init` |
| `Elet(_, _, e)` / `Ebound e` / `Eannot(_, e)` | recurse on `e` | recurse |
| everything else (leaf or does not mention sym) | `true` | `already_init` |

**Why `Ewseq` ≠ `Esseq`**: e1's `Neg` stores are not sequenced before e2, so
e2 receives `already_init` (not `ia1`).  However, both e1 and e2 always execute,
so `init_after = ia1 || ia2` (either sub-expression's store is visible to the
outer context once the `Ewseq` completes).

**`Eunseq`**: no arm's result is visible to any sibling arm.  All arms get
`already_init`; `init_after` requires every arm to have stored (intersection).

**`SeqRMW`**: atomically reads then writes.  Requires `already_init` to be safe
(the read part); leaves the variable initialised (`init_after = true`).

**`Esave` — why the conservative bail-out is necessary**: `Esave(label, args,
body)` is the loop-header form in Core.  `Erun(label, vals)` anywhere in `body`
is an unconditional back-edge jump back to the label, so `Esave` is the target of
a cycle in the control-flow graph.

A correct definite-initialisation analysis over a loop requires a **fixpoint
computation**: start with `already_init = false` at the header, analyse the body,
feed `init_after` back as the new `already_init` for the next iteration, and
repeat until stable.  `check_definitely_init` is a single syntactic descent — it
visits each node exactly once and therefore cannot model back-edges.

The hazard becomes concrete with a conditionally-storing loop:

```
Esave(L, [],
  Eif(cond,
    Esseq(_, Store0(addr=sym, …), …),
    Epure unit),            (* no store on this branch *)
  Esseq(loaded, Load0(addr=sym), …),
  … Erun(L, []) …)
```

On the first iteration where `cond` is false, the Load0 executes before any
Store0 — unsafe.  A single-pass analysis that na\"ively propagated `init_after =
true` from a prior iteration back around the back-edge would miss this.

Rather than implement fixpoint iteration, the code conservatively rejects any
variable that appears inside an `Esave` at all (returning `safe = false`).  This
is sound: a looping variable is never promoted.  The cost is rejecting cases that
are actually safe (e.g. a variable stored unconditionally on every loop iteration
before it is ever read), but those patterns are rare in front-end-generated Core
and not worth the added complexity.

## New predicate: `no_mixed_unseq_uses`

Binary operator subexpressions compile to `Eunseq` arms.  If one arm writes sym
(Store0/SeqRMW with `addr = PEsym sym`) while another arm also mentions sym, the
C semantics are an unsequenced race (UB).  Promoting sym in that case would
silently remove the Store0 and suppress Cerberus's race detector.

```
no_mixed_unseq_uses : sym -> expr -> bool
```

Walks recursively.  For each `Eunseq(arms)`:
- `writing_arms` = arms that write sym (Store0 or SeqRMW with `addr = PEsym sym`)
- `mentioning_arms` = arms that mention sym at all
- if `writing_arms ≠ []` and `|mentioning_arms| ≥ 2` → return `false`

Also recurse into each arm.

## New use variant: `Use_seqrmw`

`SeqRMW(_, _, PEsym ptr, tmp, upd)` atomically reads and writes through `ptr`.
It is promotable when `ptr = PEsym sym` — classified as `Use_seqrmw`.
If sym occurs elsewhere in the SeqRMW (in `upd_pe`) it is `Use_other`
(conservative: the pointer sym should not leak into the value computation).

## Updated `find_promotable`

```ocaml
let find_promotable ~also_fun_args f_sym body =
  let creates = collect_creates ~also_fun_args body in
  let is_promotable s =
    List.for_all use_is_promotable (collect_uses s body)
    && fst (check_definitely_init s false body)
    && no_mixed_unseq_uses s body
  in
  ...
```

## Effect on the transformation

Because `check_definitely_init` guarantees that every Load0 for a promoted symbol
is preceded by a Store0 on every path, the `transform_expr` function can assert
(or simply omit the check) that when it encounters a `Load0` for a promoted pointer,
the pointer is already in the env.  The "leave Load in place as fallback" path is
not needed.

## Test cases (0351-0356 under tests/ci/)

| File | Expected | Reason |
|---|---|---|
| `0351-mem2reg_unseq_uninit.undef.c` | UB036 | `x` uninit; Load0 in Eunseq arm with `already_init=false` |
| `0352-mem2reg_unseq_init.undef.c` | UB035 | `x` init; `check_definitely_init` passes but `no_mixed_unseq_uses` blocks (Store0 in arm2, Load0 in arm1) |
| `0353-mem2reg_unseq_reads.c` | exits 14 | `x + x` — both arms read-only; `no_mixed_unseq_uses` allows promotion |
| `0354-mem2reg_seqrmw_post.c` | exits 0 | `x++` — `Use_seqrmw`, `already_init=true` → promoted |
| `0355-mem2reg_seqrmw_pre.c` | exits 1 | `++x` — same as above |
| `0356-mem2reg_unseq_seqrmw.undef.c` | UB035 | `x + (x++)` — SeqRMW in arm2 writes; `no_mixed_unseq_uses` blocks promotion |
