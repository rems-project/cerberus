# Copy Propagation: Generalise env from `sym → sym` to `sym → pexpr`

## Context

`copy_propagation.ml` eliminates trivial bindings by substituting aliases with their source values. Its environment currently maps `sym → sym`, meaning only sym-to-sym aliases can be propagated. The goal is to generalise the env to `sym → pexpr` so that non-sym pure values (e.g. `Specified(0)`, compound pure expressions) found at the tails of effectful RHS expressions can also be propagated into body uses.

The tuple-pattern / `Eunseq` handling is deferred to a later task.

## Critical File

`ocaml_frontend/rewriters/copy_propagation.ml` — only file modified.

Also update: `ocaml_frontend/rewriters/copy_propagation.mli` (doc comment).

---

## Implementation Plan

### 1. Env type change

```ocaml
(* Old *)
type env = (Symbol.sym, Symbol.sym) Pmap.map
(* New *)
type env = (Symbol.sym, pexpr) Pmap.map
(* pexpr = (unit, Symbol.sym) generic_pexpr, in scope via `open Core` *)
```

`apply_env` is removed. Callers use `Pmap.lookup s env` directly.

```ocaml
let empty_env : env = Pmap.empty Symbol.compare_sym
let extend_env env alias pe = Pmap.add alias pe env
```

---

### 2. New helpers: `pexpr_safe` and `binders_of_pat`

`pexpr_safe binders pe` — conservative check that none of `pe`'s free syms are in `binders`. Complex forms (`PEif`, `PElet`, `PEcase`, `PEconstrained`) return `false` to avoid needing a full free-variable analysis.

```ocaml
let rec pexpr_safe binders (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s ->
      not (List.exists (fun b -> Symbol.compare_sym s b = 0) binders)
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ -> true
  | PEctor (_, pes)            -> List.for_all (pexpr_safe binders) pes
  | PEnot pe1                  -> pexpr_safe binders pe1
  | PEop (_, pe1, pe2)
  | PEwrapI (_, _, pe1, pe2)
  | PEcatch_exceptional_condition (_, _, pe1, pe2)
  | PEare_compatible (pe1, pe2)
  | PEarray_shift (pe1, _, pe2)  -> pexpr_safe binders pe1 && pexpr_safe binders pe2
  | PEmemberof (_, _, pe1)
  | PEmember_shift (pe1, _, _)
  | PEconv_int (_, pe1)
  | PEis_scalar pe1 | PEis_integer pe1
  | PEis_signed pe1 | PEis_unsigned pe1
  | PEbmc_assume pe1 | PEcfunction pe1
  | PEunion (_, _, pe1)          -> pexpr_safe binders pe1
  | PEmemop (_, pes) | PEcall (_, pes) -> List.for_all (pexpr_safe binders) pes
  | PEstruct (_, fields)         ->
      List.for_all (fun (_, pe1) -> pexpr_safe binders pe1) fields
  | PEif _ | PElet _ | PEcase _ | PEconstrained _ -> false  (* conservative *)
```

```ocaml
let rec binders_of_pat (Pattern (_, pat_)) =
  match pat_ with
  | CaseBase (None, _)   -> []
  | CaseBase (Some s, _) -> [s]
  | CaseCtor (_, pats)   -> List.concat_map binders_of_pat pats
```

---

### 3. Replace `tail_sym`/`tail_sym_acc` with `tail_pexpr`/`tail_pexpr_acc`

Returns `pexpr option` instead of `sym option`. At the `Epure pe` leaf, any safe pexpr passes (not just `PEsym`).

```ocaml
let rec tail_pexpr_acc binders (Expr (_, e_)) =
  match e_ with
  | Epure pe ->
      if pexpr_safe binders pe then Some pe else None
  | Ewseq (pat, _, e2) | Esseq (pat, _, e2) ->
      tail_pexpr_acc (binders_of_pat pat @ binders) e2
  | Elet (pat, _, e2) ->
      tail_pexpr_acc (binders_of_pat pat @ binders) e2
  | Ebound e | Eannot (_, e) ->
      tail_pexpr_acc binders e
  | _ -> None

let tail_pexpr e = tail_pexpr_acc [] e
```

Key differences from `tail_sym_acc`:
- `Epure pe` leaf returns `Some pe` for any safe pexpr (not just `PEsym s`).
- Uses `binders_of_pat` which handles `CaseCtor` tuple patterns (old code only tracked `CaseBase(Some s)` binders).

---

### 4. Update `propagate_pexpr`

**`PEsym s`** — return the stored pexpr directly if found:
```ocaml
| PEsym s ->
    (match Pmap.lookup s env with
     | Some pe -> pe
     | None    -> Pexpr (annots, bty, PEsym s))
```

**`PElet CaseBase(Some alias)` with `PEsym src` RHS** — look up `src` in env to get its pexpr, store that for `alias`:
```ocaml
| PElet (Pattern (p_annots, CaseBase (Some alias, cbty)),
         (Pexpr (_, _, PEsym src) as rhs), body) ->
    let pe_src = match Pmap.lookup src env with
                 | Some pe -> pe
                 | None    -> rhs in
    Pexpr (annots, bty,
      PElet (Pattern (p_annots, CaseBase (None, cbty)),
             propagate_pexpr env rhs,
             propagate_pexpr (extend_env env alias pe_src) body))
```

The existing `_ ->` fallthrough arm is unchanged (don't propagate non-PEsym `Elet` RHS).

---

### 5. Update `propagate_expr`

**`Ewseq`/`Esseq CaseBase(Some alias)`** — switch `tail_sym` to `tail_pexpr`; store `pexpr` in env:
```ocaml
| Ewseq (Pattern (p_annots, CaseBase (Some alias, cbty)), e1, body) ->
    let e1' = propagate_expr env e1 in
    (match tail_pexpr e1' with
     | Some pe ->
         Expr (annots, Ewseq (Pattern (p_annots, CaseBase (None, cbty)),
                              e1',
                              propagate_expr (extend_env env alias pe) body))
     | None ->
         Expr (annots, Ewseq (Pattern (p_annots, CaseBase (Some alias, cbty)),
                              e1',
                              propagate_expr env body)))
(* Symmetric for Esseq *)
```

Note: `tail_pexpr e1'` is called on the already-propagated `e1'`, so the extracted pexpr is already in canonical form.

**`Elet CaseBase(Some alias)` with `PEsym src` RHS** — use `Pmap.lookup` instead of old `apply_env`:
```ocaml
| Elet (Pattern (p_annots, CaseBase (Some alias, cbty)), pe1, body) ->
    (match pe1 with
     | Pexpr (_, _, PEsym src) ->
         let pe_src = match Pmap.lookup src env with
                      | Some pe -> pe
                      | None    -> pe1 in
         Expr (annots,
           Elet (Pattern (p_annots, CaseBase (None, cbty)),
                 propagate_pexpr env pe1,
                 propagate_expr (extend_env env alias pe_src) body))
     | _ ->
         Expr (annots,
           Elet (Pattern (p_annots, CaseBase (Some alias, cbty)),
                 propagate_pexpr env pe1,
                 propagate_expr env body)))
```

All other arms (`Ewseq (pat, e1, e2)`, `Esseq (pat, e1, e2)`, `Elet (pat, pe1, e2)` catch-alls, and all other expr forms) are structurally unchanged — just propagate recursively.

---

## Design Notes

- **Annotation loss at substitution site** is acceptable: `bty = unit` throughout untyped Core; occurrence-site annots on `PEsym` nodes are typically empty.
- **`Elet` CaseBase arm stays conservative** (PEsym RHS only): avoids expression explosion for non-trivial pure let bindings. The generalisation only affects the VALUES stored in the env (now pexprs) and the VALUES extracted via `tail_pexpr` (now any safe pure expr, not just PEsym).
- **`binders_of_pat` replaces the inline `CaseBase(Some s, _)` extraction** in `tail_sym_acc`. The new version correctly handles `CaseCtor` tuple patterns — if a chain contains a `let (a, b) = ...` binding, both `a` and `b` are now added to `binders`, preventing either from leaking via `tail_pexpr`.
- **No generic equality used**: avoid `bindings = []`; pattern-match on `[]` instead.

---

## `.mli` Update

```ocaml
(** Pure expression rebinding elimination.

    Eliminates bindings of the form [let alias = pure(e) in body] by
    substituting [e] for [alias] throughout [body].  The binding node is
    preserved (pattern replaced by a wildcard) so that source-location
    annotations are not lost.

    Handles:
    - {b Single named bindings} ([CaseBase(Some alias, _)]) against
      [pure(sym)] (pure let) or effectful RHS whose tail is [pure(e)].
      The tail [e] may be any pure expression, not just a symbol alias.

    No memory events, sequencing, or values are changed. *)

val transform_file : unit Core.file -> unit Core.file
```

---

## Verification

```sh
make && make install
cd tests && USE_OPAM='' bash run-ci.sh  # all existing tests must pass
USE_OPAM='' bash run-copy-prop.sh       # including with copy-prop
```

Write doc history: `doc/history/2026-03-23_copy-prop-pexpr-env.md`.
