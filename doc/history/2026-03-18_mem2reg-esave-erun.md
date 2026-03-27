# Plan: Esave/Erun support in mem2reg analysis

## Context

The mem2reg analysis in `ocaml_frontend/rewriters/core_mem2reg.ml` conservatively
rejects every variable that appears inside any `Esave` or `Erun`.

**Elaboration invariants:**

1. **Default args** of `Esave` are always addresses of C locals in scope:
   `Esave(L, [(param, (_, PEsym ptr)), ...], body)`.
2. **The body** of `Esave` refers **only** to its declared parameter syms — not
   the outer ptr syms, not even in nested `Erun` args.

   > **[Correction]** This invariant is **too strong** and does not hold in
   > practice.  Non-CREATE-bound syms — most notably function-parameter pointers
   > (e.g. `n` in `int fact(int n)`) — can appear freely in an Esave body without
   > being passed as params.  The elaboration only threads **CREATE-bound local
   > pointer syms** through Esave params; other in-scope syms (function parameters,
   > globals) are referenced directly from the body.  The correct, weaker invariant
   > is: **for any CREATE-bound local pointer sym `s`, every occurrence of `s`
   > inside an Esave body is via a param that aliases `s` as a bare `PEsym`**.
   > This is sufficient to justify the NoAlias shortcut in `collect_uses` and
   > `check_definitely_init`.

3. **`Erun` args** are always addresses of local vars in the *current* scope.
   Inside an `Esave` body the current scope is the param syms, so back-edge Erun
   args are param syms.  Outside an `Esave` they are outer ptr syms.
4. **`Erun` is terminal**: control flows *into* Erun but never out of it.
   `init_after` for an Erun is vacuously `true` (the continuation is unreachable).
5. **`Erun` scope**: can appear as a forward jump, backward jump, or recursive
   back-edge inside an Esave body.  Not necessarily nested inside the target Esave.
6. **Escape propagation**: if `param_sym` escapes (gets `Use_other`) in an Esave
   body, then the default arg and **all** `Erun` args to that label at that
   parameter position are also considered escaping.

## Critical file

`ocaml_frontend/rewriters/core_mem2reg.ml`

---

## Design

### Key insight: memoize per-Esave analysis on demand

Both `collect_uses` and `check_definitely_init` share a need to analyse Esave bodies: once when entering via a default arg, and once per `Erun` call site.  Rather than a pre-compute pass, we memoize results keyed by `(label_sym, param_position)`.  On the first demand the body is traversed; subsequent requests hit the cache.

---

### Function signatures

```ocaml
val collect_uses
  :  use_memo_info
  -> Symbol.sym
  -> ('a, 'b, Symbol.sym) generic_expr
  -> use list

val check_definitely_init
  :  init_memo_info
  -> Symbol.sym
  -> bool                               (* already_init *)
  -> ('a, 'b, Symbol.sym) generic_expr
  -> bool * bool                        (* safe, init_after *)
```

### New data structures

```ocaml
(* One entry per Esave label in the memo table. *)
type 'a esave_memo_entry = {
  params  : (Symbol.sym * pexpr) list;            (* (param_sym, default_pe) by position *)
  body    : (unit, unit, Symbol.sym) generic_expr;
  results : (Symbol.sym, 'a) Pmap.map ref;        (* param_sym -> cached result, filled lazily *)
}

(* 'a = use list        for collect_uses                                    *)
(* 'a = bool * bool     for check_definitely_init  (safe_uninit, inits_param) *)
(*   safe_uninit:   fst (check_definitely_init ... param_sym false body)    *)
(*   inits_param:   snd (check_definitely_init ... param_sym false body)    *)
type 'a memo_save_info = (Symbol.sym, 'a esave_memo_entry) Pmap.map
```

A **pre-walk** (`collect_esave_defs : expr -> 'a memo_save_info`)
populates every `Esave` label with its `params` and `body`, leaving `results`
as `ref Pmap.empty`.  This enables `Erun` call sites to resolve forward references.

`find_promotable` calls `collect_esave_defs` once to get `use_memo`, then derives
`init_memo` by mapping each entry to a new record with a fresh `ref Pmap.empty`
(reusing `params` and `body`).

**Closedness check** (performed in `collect_esave_defs`): for each `Esave(L,
params, body)`, perform two defensive checks, both signalling
`failwith "Core_mem2reg: ..."` on failure:

1. *Direct-alias args*: every default arg `pe` in `params` is a bare `PEsym` —
   i.e., `is_pesym some_sym pe`.  A complex default arg would mean the param
   cannot be a direct pointer alias.
2. *Body closedness*: traverse `body` with a **bound-variable environment**
   (a `Symbol.sym` set) initialised with the declared `param_sym`s.  As the
   traversal descends into binding forms it extends the environment:
   - `Esseq`/`Ewseq` patterns bind the LHS sym before descending into the RHS.
   - `Elet(_, sym, e)` binds `sym` before descending into `e`.
   - Inner `Esave(L', params', body')` binds each `param_sym'` before descending
     into `body'` (but NOT into the default args of `params'`, which belong to
     the outer scope).
   Whenever a sym is *used* (as a `PEsym` in a pexpr, or as a load/store address,
   or as an Erun argument) and is not in the current environment, call
   `failwith "Core_mem2reg: Esave body not closed — free sym"`.

   <!-- Note: Core type-checking can/should be adjusted so that Esaves are
        checked to be closed in this way too, making this a re-enforcement of
        a property already guaranteed by construction. -->

These are defensive checks against future elaboration changes.  When both pass,
the `NoAlias` cases in `collect_uses` and `check_definitely_init` can safely
skip the body.

> **[Correction]** Both checks were removed during implementation:
>
> - *Check 1 (direct-alias args)* was removed first.  The `ret_509` return label
>   generated by the elaborator has a non-loop-carried default arg of `Specified(0)`
>   (not a bare `PEsym`), causing a spurious failure on every function.
>
> - *Check 2 (body closedness)* was removed next.  Tests `0015-while_break.c`,
>   `0016-do_break.c`, `0017-for_simple.c`, `0021-fact.c`, `0022-while_continue.c`,
>   `0054-while_factorial5.c`, `0070-do-while1.c`, `0071-do-while2.c`,
>   `0126-duff_device.c`, and `0317-compound-literal-lifetime.c` all failed because
>   their loop Esave bodies freely reference function-parameter pointer syms that
>   are not Esave params (see corrected Invariant 2 above).  A separate bug was also
>   found: the `SeqRMW` action binds a sym in its update lambda (`a_537 => ...`)
>   that the traversal forgot to add to the environment; this was fixed before the
>   check was removed.
>
> The NoAlias shortcut is still sound, justified by the **corrected** Invariant 2
> (the elaboration only threads CREATE-bound syms through params), not by global
> body closedness.

**One-pass sufficiency:**
- `collect_uses`: the sentinel `results[param_sym] = []` for back-edges is exact.
  A back-edge `Erun(L, [param])` passes the alias with no semantic value-use;
  `[]` is the correct result, not an approximation.
- `check_definitely_init`: no fixpoint is needed.  For an `Erun(L, args)` where
  `args[i] = PEsym sym`, control jumps unconditionally to the body of `Esave L`
  with `param_sym` (at position i) receiving sym's current init state.  The
  sequential continuation after the `Erun` is unreachable, so `init_after = true`.
  Safety is `already_init || safe_uninit` where `safe_uninit` is computed for the
  target param.  For a back-edge `Erun` (inside the body currently being analysed),
  the sentinel `safe_uninit = true` is used; this is an over-approximation but is
  safe: the over-approximation of `safe_uninit` can only make the outer Eif/Ecase
  more optimistic about the back-edge branch, while the non-back-edge exit paths
  are computed exactly.  Concretely, if a load-before-store exists on any exit path,
  that path still computes `safe = false` regardless of the sentinel.

---

### Helper: `find_single_direct_alias sym pairs`

```ocaml
(* Given an association list of (param_sym, pe) pairs, returns:
     None           — sym does not appear as a bare PEsym in any pe
     Some param_sym — sym appears as a bare PEsym in exactly one pe
   Raises failwith if sym appears in more than one pe (invariant violation). *)
let find_single_direct_alias sym pairs =
  match List.filter_map (fun (param_sym, pe) ->
    if is_pesym sym pe then Some param_sym else None) pairs
  with
  | []          -> None
  | [param_sym] -> Some param_sym
  | _           -> failwith "Core_mem2reg: multiple direct aliases for the same sym"
```

The Esave and Erun cases in both `collect_uses` and `check_definitely_init` follow
the same pattern: look up the Esave entry in the memo by label, find the aliased
`param_sym` via `find_single_direct_alias`, then either return the cached result or
compute it (with sentinel pre-fill for back-edge termination).

### Change 1: `collect_uses` — Esave case

```ocaml
| Esave ((label_sym, _), params, _body) ->
    (* All default args are bare PEsym by the closedness check.
       Closedness also guarantees sym is not free in body unless it is a param. *)
    let entry = Pmap.find label_sym use_memo in
    (match find_single_direct_alias sym (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
    | None           -> []   (* NoAlias: by closedness, not in body *)
    | Some param_sym ->
        (match Pmap.lookup param_sym !(entry.results) with
        | Some cached -> cached
        | None ->
            entry.results := Pmap.add param_sym [] !(entry.results);  (* sentinel *)
            let result = collect_uses use_memo param_sym entry.body in
            entry.results := Pmap.add param_sym result !(entry.results);
            result))
```

### Change 2: `collect_uses` — Erun case

```ocaml
| Erun (_, label_sym, args) ->
    (* Closedness guarantees args matching sym are direct PEsym aliases. *)
    let entry = Pmap.find label_sym use_memo in
    (match find_single_direct_alias sym (List.combine (List.map fst entry.params) args) with
    | None           -> []
    | Some param_sym ->
        (match Pmap.lookup param_sym !(entry.results) with
        | Some cached -> cached
        | None ->
            entry.results := Pmap.add param_sym [] !(entry.results);
            let result = collect_uses use_memo param_sym entry.body in
            entry.results := Pmap.add param_sym result !(entry.results);
            result))
```

---

### Change 3: `check_definitely_init` — Esave case

```ocaml
| Esave ((label_sym, _), params, _body) ->
    let entry = Pmap.find label_sym init_memo in
    (match find_single_direct_alias sym (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
    | None           -> (true, already_init)  (* NoAlias: by closedness, not in body *)
    | Some param_sym ->
        let (safe_uninit, inits_param) =
          match Pmap.lookup param_sym !(entry.results) with
          | Some cached -> cached
          | None ->
              (* Sentinel (true, true): safe over-approximation for back-edge Eruns.
                 Any load-before-store in the body is encountered sequentially
                 *before* the back-edge Erun in the analysis.  That load sets
                 safe=false, which propagates through && rules regardless of the
                 sentinel.  The sentinel therefore cannot mask a real unsafety.
                 Using (false,false) instead would over-conservatively reject safe
                 loops; (true,true) is the minimal sound choice. *)
              entry.results := Pmap.add param_sym (true, true) !(entry.results);
              let r = check_definitely_init init_memo param_sym false entry.body in
              entry.results := Pmap.add param_sym r !(entry.results);
              r
        in
        (* already_init: the local var can be loaded during transform at this
             default-arg use point (sym has been stored on all incoming paths).
           safe_uninit: the parameter does not need to be initialized going in
             (the body always stores before loading on every control-flow path).
           The || says the transform can still proceed in either case:
             - already_init → we can emit a Load here to pass the current value in
             - safe_uninit  → we can drop this arg; the body self-initializes
           inits_param: the body unconditionally writes param_sym before completion,
             so sym's storage is definitely initialized after the Esave exits.
           already_init || inits_param: sym is init after Esave if it was init
             going in, or the body always initializes param_sym. *)
        (already_init || safe_uninit, already_init || inits_param))
```

### Change 4: `check_definitely_init` — Erun case (add explicit case)

```ocaml
| Erun (_, label_sym, args) ->
    (* Erun unconditionally jumps to Esave L's body.
       init_after = true: the sequential continuation is unreachable.
       Closedness guarantees all Erun args matching sym are direct PEsym aliases
       (no structural occurrences), so no structural check is needed here. *)
    let entry = Pmap.find label_sym init_memo in
    let safe =
      match find_single_direct_alias sym (List.combine (List.map fst entry.params) args) with
      | None           -> true   (* sym not in args; vacuously safe *)
      | Some param_sym ->
          let (safe_uninit, _) =
            match Pmap.lookup param_sym !(entry.results) with
            | Some cached -> cached
            | None ->
                (* Sentinel (true, true): same reasoning as Esave case above. *)
                entry.results := Pmap.add param_sym (true, true) !(entry.results);
                let r = check_definitely_init init_memo param_sym false entry.body in
                entry.results := Pmap.add param_sym r !(entry.results);
                r
          in
          (* already_init: the local var can be loaded during transform at this
               Erun arg use point (sym has been stored on all incoming paths).
             safe_uninit: the parameter does not need to be initialized going in.
             The || says the transform can still proceed in either case:
               - already_init → we can emit a Load here to pass the current value
               - safe_uninit  → we can drop this arg; the body self-initializes
             init_after = true: Erun is terminal; the continuation is unreachable. *)
          already_init || safe_uninit
    in
    (safe, true)
```

---

### Change 5: `no_mixed_unseq_uses` — Esave case

No memo needed; delegates to param directly using `find_single_direct_alias`:

```ocaml
| Esave (_, params, body) ->
    (match find_single_direct_alias sym (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
    | None           -> true
    | Some param_sym -> no_mixed_unseq_uses param_sym body)
```

### Change 6: `expr_writes_sym` — Esave case

```ocaml
| Esave (_, params, body) ->
    (match find_single_direct_alias sym (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
    | None           -> false
    | Some param_sym -> expr_writes_sym param_sym body)
```

---

### Update `find_promotable`

```ocaml
let find_promotable ~also_fun_args f_sym body =
  let use_memo  : use list memo_save_info = collect_esave_defs body in
  let init_memo : (bool * bool) memo_save_info =
    Pmap.map (fun { params; body; _ } ->
      { params; body; results = ref Pmap.empty }) use_memo in
  let creates = collect_creates ~also_fun_args body in
  let is_promotable s =
    List.for_all use_is_promotable (collect_uses use_memo s body)
    && fst (check_definitely_init init_memo s false body)
    && no_mixed_unseq_uses s body
  in
  ...
```

`collect_esave_defs` is a simple recursive walk that builds the `memo_save_info`
with empty `results` maps.  `no_mixed_unseq_uses` and `expr_writes_sym` do not
recurse through Erun and need no memo tables.

---

## Test cases to add under `tests/ci/`

| File | Expected | Scenario |
|---|---|---|
| `0361-mem2reg_loop_read_preinit.c` | exits 42 | Var init'd before loop, only **read** inside loop body |
| `0362-mem2reg_loop_escape.c` | exits 0 | Loop body calls `fn(&x)` — param escapes → NOT promoted |
| `0363-mem2reg_nested_loops.c` | exits 3 | Outer var read inside inner loop — nested Esave alias |
| `0364-mem2reg_loop_uninit_load.c` | UB | `int x; do { x; } while (x > 0); return x;` — uninit load inside do-while; sentinel `(true,true)` must not mask it |

---

## History file

Per `CLAUDE.md`, copy plan to `doc/history/2026-03-18_mem2reg-esave-erun.md`.

---

## Verification

```sh
make && make install

cd tests
USE_OPAM='' bash run-ci.sh 2>&1 | grep -E "036[1-4]"

# Full suite
USE_OPAM='' bash run-ci.sh

# Debug: check which vars are marked promotable
cerberus --sw mem2reg --verbosity=3 tests/ci/0361-mem2reg_loop_read_preinit.c \
  2>&1 | grep mem2reg
```
