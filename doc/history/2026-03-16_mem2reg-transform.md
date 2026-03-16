# Plan: mem2reg Phase 2 — Transformation Pass

## Context

`core_mem2reg.ml` has a complete Phase 1 (analysis: `collect_creates`,
`collect_uses`, `find_promotable`) but `transform_file` is still a stub that
returns the file unchanged.  Phase 2 implements the actual transformation.

The rationale for hand-rolling rather than using `core_rewriter` is in
`2026-03-16_mem2reg-core-rewriter.md`.  The definite-assignment analysis fix that
Phase 2 depends on is in `2026-03-16_mem2reg-definite-assignment.md`.

---

## Key files

| File | Change |
|---|---|
| `ocaml_frontend/rewriters/core_mem2reg.ml` | Add `type env`, `check_definitely_init`, `transform_expr`, `thread_branch`, update `transform_file` |
| `ocaml_frontend/rewriters/core_mem2reg.mli` | No change (interface already correct) |

---

## New types

```ocaml
(* Maps ptr_sym -> current val_sym (last-stored value) *)
type env = (Symbol.sym * Symbol.sym) list
```

Helper: `lookup : env -> Symbol.sym -> Symbol.sym option`

---

## `transform_expr` — straight-line cases

Signature:
```ocaml
val transform_expr
  :  env
  -> Symbol.SSet.t
  -> (unit, unit) Core.generic_expr
  -> (unit, unit) Core.generic_expr
```

### Create (promotable)

Drop the `Esseq(…, Create(PrefSource _), body)` node entirely; recurse on `body`
with the same env.

### Store (promotable)

```
Esseq(_, Eaction(Store0(_, _, PEsym ptr_x, val_pe, _)), cont)
→ Elet(CaseBase(new_sym, bty), Epure(val_pe),
       transform_expr (env[ptr_x ↦ new_sym]) promotable cont)
```

`new_sym` is minted via `Cerb_fresh.fresh_sym ()`.  `bty` is the base type of the
stored value (extracted from the Store0 type argument).

### Load (promotable, ptr_x ∈ dom(env))

```
Esseq(CaseBase(Some loaded_x, bty), Eaction(Load0(_, PEsym ptr_x, _)), cont)
→ Elet(CaseBase(loaded_x, bty), Epure(PEsym (lookup env ptr_x)),
       transform_expr env promotable cont)
```

Because `check_definitely_init` guarantees every Load is preceded by a Store on
every path, `ptr_x` is always in `dom(env)` when reached.  No fallback is needed.

### Kill (promotable)

Drop `Esseq(_, Eaction(Kill(_, PEsym ptr_x)), cont)`; recurse on `cont` unchanged.

### All other nodes

Structural recursion — recurse into sub-expressions with the current env unchanged.

---

## `thread_branch` — branch helper

When branching, some promotable pointer variables may be written inside one or
more arms.  After the branch those updated values must be available in the
continuation.  `thread_branch` transforms one arm and arranges for the current
value of each variable in `to_thread` to be returned as an extra element of the
arm's result.

```ocaml
val thread_branch
  :  env
  -> Symbol.SSet.t            (* promotable *)
  -> Symbol.sym list          (* ptr_syms whose values must be threaded out *)
  -> (unit, unit) Core.generic_expr
  -> Symbol.sym list          (* fresh val_syms, one per threaded ptr *)
   * (unit, unit) Core.generic_expr  (* transformed arm *)
```

Implementation: transform the arm body normally, then wrap its final expression so
that the innermost continuation returns a tuple
`Epure(PEtuple [original_val; PEsym v_1; …; PEsym v_n])` where each `v_i` is
`lookup env' ptr_i` in the env *after* transforming the arm (`env'`).

The caller is responsible for picking a *single* set of `phi_sym`s for the whole
join point (one fresh sym per threaded ptr), then destructuring the tuple result to
bind them.

---

## `transform_expr` — branching: `Eif`

For `Esseq(unit_pat, Eif(cond, e_true, e_false), cont)`:

1. Compute `written` = `{ptr_x ∈ promotable | Store0(ptr_x) appears in e_true or e_false}`.
2. **No writes** (`written = ∅`): transform both branches and `cont` with the same env; reconstruct `Esseq(unit_pat, Eif(cond, e_true', e_false'), cont')`.
3. **Writes present**:
   - `to_thread = SSet.elements written`
   - Call `thread_branch env promotable to_thread e_true` → `(val_syms_t, e_true')`
   - Call `thread_branch env promotable to_thread e_false` → `(val_syms_f, e_false')`
   - Mint one `phi_sym_x` per element of `to_thread`
   - Build result pattern: `CaseTuple [unit_pat; CaseBase(phi_1, bty_1); …]`
   - Build `env'` = env extended with `ptr_x ↦ phi_sym_x` for each written ptr
   - Return:
     ```
     Esseq(result_pat, Eif(cond, e_true', e_false'),
           transform_expr env' promotable cont)
     ```

`Ecase` is handled analogously: union of `written` over all arms; one
`thread_branch` call per arm.

---

## Updated `transform_file`

```ocaml
let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  let transform_decl f_sym decl =
    match decl with
    | Proc (annots, loc, params, ret_ty, body) ->
        let promotable = find_promotable ~also_fun_args f_sym body in
        let promotable_set =
          List.fold_left (fun s x -> Symbol.SSet.add x s) Symbol.SSet.empty promotable
        in
        let body' = transform_expr [] promotable_set body in
        Proc (annots, loc, params, ret_ty, body')
    | Fun _ | ProcDecl _ | BuiltinDecl _ -> decl
  in
  { file with funs = Pmap.mapi transform_decl file.funs }
```

---

## Verification

```sh
make && make install

# Core IR inspection — Create/Kill must be gone for simple locals
cerberus --pp core --sw mem2reg tests/ci/mem2reg_simple.c

# Create/Kill must remain for non-promotable vars (address taken)
cerberus --pp core --sw mem2reg tests/ci/mem2reg_no_promote_address.c

# Typecheck transformed output
cerberus --typecheck-core --sw mem2reg tests/ci/mem2reg_*.c

# Regression: output must be identical with and without the pass
cd tests
USE_OPAM='' bash run-mem2reg.sh
```
