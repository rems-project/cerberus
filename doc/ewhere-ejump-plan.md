# Plan: Add `Ewhere` / `Ejump` to Core IR

## Context

The user added two new constructors to `generic_expr_` in `frontend/model/core.lem`:

- **`Ejump`** – identical to `Erun` in every pass (same field layout, same semantics)
- **`Ewhere`** – similar to `Esave` but defines a **block of mutually recursive labels**

The type definition had two bugs discovered during planning:
1. `Ewhere`'s field 2 `('sym * core_base_type)` was a mistake and must be **removed**
2. Each element of `Ewhere`'s list must include its own `('sym * core_base_type)`, i.e. become `list (('sym * core_base_type) * params_list * generic_expr)`

The generated `ocaml_frontend/generated/core.ml` was regenerated already (from the pre-fix `core.lem`), so it has the *wrong* type. After fixing `core.lem`, all generated files must be regenerated via `make`.

Build fails with exhaustiveness-check errors (`-w @8`) on these files:
- `ocaml_frontend/generated/core_sequentialise.ml`
- `ocaml_frontend/generated/core_linking.ml`
- `ocaml_frontend/generated/core_aux.ml` (9 functions)
- `ocaml_frontend/rewriters/core_rewriter.ml`
- `ocaml_frontend/rewriters/copy_propagation.ml`
- `ocaml_frontend/pprinters/pp_core.ml`

Additional files will fail once the above are fixed (dune stops at first errors due to dependency order):
- `ocaml_frontend/generated/core_rewrite.ml`, `core_run.ml`, `core_reduction.ml`, `core_typing.ml`, `core_indet.ml`, `core_run_aux.ml`
- `ocaml_frontend/rewriters/core_peval.ml`
- `ocaml_frontend/milicore.ml`

---

## Corrected type definitions

### `frontend/model/core.lem`

Replace (lines 336-337):
```lem
| Ewhere of (generic_expr 'a 'bty 'sym) * ('sym * core_base_type) * list (list ('sym * (core_base_type * maybe (Ctype.ctype * pass_by_value_or_pointer))) * (generic_expr 'a 'bty 'sym))
| Ejump of 'a * 'sym * list (generic_pexpr 'bty 'sym)
```

With:
```lem
| Ewhere of (generic_expr 'a 'bty 'sym) * list (('sym * core_base_type) * list ('sym * (core_base_type * maybe (Ctype.ctype * pass_by_value_or_pointer))) * (generic_expr 'a 'bty 'sym))
| Ejump of 'a * 'sym * list (generic_pexpr 'bty 'sym)
```

---

## Step-by-step implementation

### Phase 1 – Fix Lem sources (regenerated automatically by `make`)

**Pattern to apply everywhere:**

- `Ejump` cases are **identical to `Erun`** cases (same signature, same structure)
- `Ewhere e defs` cases recurse into `e` and each `body` in `defs`; bind `params` of each def like `Esave` binds its param list

#### `frontend/model/core_sequentialise.lem`

After the `Erun` case (line 57), add:
```lem
| Ewhere e cases ->
    Ewhere (sequentialise_expr e)
      (List.map (fun (sym_ty, params, body) -> (sym_ty, params, sequentialise_expr body)) cases)
| Ejump () sym es ->
    expr_
```

#### `frontend/model/core_aux.lem` (9 functions)

Each function gets `Ejump` like its `Erun` case and `Ewhere` like an `Esave`-over-list.
Any functions looking for Eruns/Esaves should skip Ejump/Ewhere - they will be mutually exclusive: programs with the former will be transformed into the latter by a future Core rewriter.

| Function (line) | `Ejump` | `Ewhere` |
|---|---|---|
| `subst_sym_expr` (1030) | `Ejump annot lab_sym (List.map (subst_sym_pexpr sym cval) pes)` | subst into `e` + each body; skip body if param shadows sym |
| `unsafe_subst_sym_expr` (1299) | same with `unsafe_subst_sym_pexpr` | same |
| `to_pure` (1574) | `Nothing` | `Nothing` |
| `subst_wait` (1649) | `expr_` | recurse `e` and each body |
| `find_labeled_continuation` (1748) | `Nothing` | `Nothing` (Ejump/Ewhere and Erun/Esave will be mutually exclusive) |
| `find_labeled_continuation2_aux` (1827) | `acc` | `acc` |
| `collect_labeled_continuations` (1911) | `Map.empty` | `Map.empty` |
| `collect_saves_aux` (2240) | `st` | `st` |
| `m_collect_saves_aux` (2352) | `st` | `st` |

Specific code for `subst_sym_expr` Ewhere:
```lem
| Ewhere e cases ->
    let cases' = List.map (fun (sym_ty, params, body) ->
      (sym_ty, params,
       if List.any (fun (z, _) -> sym = z) params then body
       else subst_sym_expr sym cval body)
    ) cases in
    Ewhere (subst_sym_expr sym cval e) cases'
```

#### `frontend/model/core_linking.lem` (after line 215)

```lem
| Ewhere _ _ ->
    error ("TODO: free_expr Ewhere")
| Ejump _ _ _  ->
    error ("TODO: free_expr Ejump")
```

#### `frontend/model/core_indet.lem`

`indet_hack` (after `Erun` case, line 436):
```lem
| Core.Ewhere e defs ->
    Core.Expr annot (Core.Ewhere (indet_hack e)
      (List.map (fun (sym_ty, params, body) -> (sym_ty, params, indet_hack body)) defs))
| Core.Ejump _ _ _ ->
    expr
```

`import_expr` (after `Erun` case, line 153):
```lem
| Core.Ewhere _ _ -> error "import_expr: Ewhere not supported in indet"
| Core.Ejump _ _ _ -> error "import_expr: Ejump not supported in indet"
```

#### `frontend/model/core_rewrite.lem` (8 active functions)

All follow the same pattern. For functions that **transform pexprs** (e.g. `remove_conv_int`):
```lem
| Ewhere e cases ->
    Ewhere (remove_conv_int e)
      (List.map (fun (sym_ty, params, body) ->
        (sym_ty, params, remove_conv_int body)) cases)
| Ejump annot sym pes ->
    Ejump annot sym (List.map remove_conv_int_pexpr pes)
```

For functions that **just traverse** (e.g. `remove_skips`, `remove_unseqs`, `sequentialise_creates_kills`, `pure_propagation2`, `simpl_case`):
```lem
| Ewhere e cases ->
    Ewhere (f e) (List.map (fun (sym_ty, params, body) -> (sym_ty, params, f body)) cases)
| Ejump _ _ _ ->
    expr_
```
where `f` is the recursive function and `expr_` is returned unchanged for `Ejump`.

Note: `remove_seqs` and `pure_propagation` are commented out in the source — no changes needed there.

Note: The `rewriter` record type has dead `save_rwter`/`run_rwter` fields that are never called. Do **not** add `where_rwter`/`jump_rwter` fields — the existing pattern-match functions handle constructors directly without the record.

#### `frontend/model/core_rewrite2.lem`

Add to the `alg_type` record (after `a_Erun`, line 314):
```lem
; a_Ewhere : 'expr -> list (('sym * core_base_type) * list ('sym * (core_base_type * maybe (Ctype.ctype * pass_by_value_or_pointer))) * 'expr) -> exceptM 'expr_ msg
; a_Ejump : 'a -> 'sym -> list 'pexpr -> exceptM 'expr_ msg
```

Add to `fold_expr` (after `Erun` case, line 386):
```lem
| Ewhere e defs ->
   (fold_expr alg e) >>= fun e ->
   (mapM (fun (sym_ty, params, body) ->
     fold_expr alg body >>= fun body' -> return (sym_ty, params, body')
   ) defs) >>= fun defs ->
   wrap (alg.a_Ewhere e defs)
| Ejump a s pes ->
   (mapM (fold_pexpr alg.pexpr_alg) pes) >>= fun pes ->
   wrap (alg.a_Ejump a s pes)
```

Add to both default algebra records (after `a_Erun`, lines 501 and 676):
```lem
; a_Ewhere = fun e defs -> return (Ewhere e defs)
; a_Ejump = fun a b c -> return (Ejump a b c)
```

#### `frontend/model/core_unstruct.lem` (after `Erun`, line 332)

```lem
| Ewhere _ _ ->
    expr
| Ejump _ _ _ ->
    expr
```

#### `frontend/model/core_typing.lem`

Keep the labs field in the env record for saves only, add a separate one for where-labels.
Explain the context and then ask the user how to proceed for this.

`collect_labels` (after `Erun`, line 1643):
`typecheck_expr` (after `Erun`, line 1838):

#### `frontend/model/core_run_aux.lem` (3 locations)

`add_to_sb` (after `Erun`, line 350):
```lem
| Ewhere e cases ->
    Ewhere (add_to_sb p_aids e)
      (List.map (fun (sym_ty, params, body) -> (sym_ty, params, add_to_sb p_aids body)) cases)
| Ejump annots sym pes ->
    Ejump <| annots with sb_before= (Set.map snd p_aids) union annots.sb_before |> sym pes
```

`add_to_asw` (after `Erun`, line 435):
```lem
| Ewhere e cases ->
    Ewhere (add_to_asw aids e)
      (List.map (fun (sym_ty, params, body) -> (sym_ty, params, add_to_asw aids body)) cases)
| Ejump annots sym pes ->
    Ejump <| annots with asw_before= aids union annots.asw_before |> sym pes
```

`convert_expr` (after `Erun`, line 600):
```lem
| Ewhere e cases ->
    Ewhere (convert_expr e)
      (List.map (fun (sym_ty, params, body) -> (sym_ty, params, convert_expr body)) cases)
| Ejump _ sym pes ->
    Ejump empty_annotation sym (List.map convert_pexpr pes)
```

#### `frontend/model/core_run.lem`

In the big `(arena_expr_, stack)` pattern match (after `Erun`, line 1530).
Explain the context and then ask the user how to proceed for all of these.

```lem
| (Ewhere e _, _) ->
    (* explain and ask *)
    one $ Step_tau "Ewhere" TSK_Misc begin
      E.return <| th_st with arena= e |>
    end

| (Ejump _ _ _, Stack_empty) ->
    (* explain and ask *)
    error "reached empty stack with an Ejump"

| (Ejump _ _ _, Stack_cons Nothing _ _) ->
    (* explain and ask *)
    error "found a Ejump outside of a procedure"

| (Ejump annots sym pes, Stack_cons (Just current_proc) cont sk) ->
    (* explain and ask *)
```

Also add to `has_ccall` (after `Erun`, ~line 476):
```lem
| Ejump _ _ _ -> false
| Ewhere e defs -> has_ccall e || List.any (fun (_, _, body) -> has_ccall body) defs
```

#### `frontend/model/core_reduction.lem`

Explain the context and then ask the user how to proceed for all of these.

```lem
| Ewhere _ _ ->
    (* explain and ask *)
| Ejump _ _ _ ->
    (* explain and ask *)
```

---

### Phase 2 – Regenerate generated files

Run `make` from the repo root. This runs Lem on all `$(LEM_SRC)` and regenerates `ocaml_frontend/generated/*.ml`. The Lem tool itself will only warn on non-exhaustive patterns (`-wl_pat_exh warn`), but the regenerated `.ml` files will now have the correct type and all the new cases added above.

---

### Phase 3 – Update non-generated OCaml files

These match on `Core.*` types directly and must be updated **after** the type is regenerated.

#### `ocaml_frontend/rewriters/core_rewriter.ml` (after `Erun`, line 397)

```ocaml
| Ewhere (e, defs) ->
    mapM (fun (sym_ty, params, body) ->
      aux body >>= fun body' ->
      return (sym_ty, params, body')
    ) defs >>= fun defs' ->
    aux e >>= fun e' ->
    return_wrap (Ewhere (e', defs'))
| Ejump ((), sym, pes) ->
    mapM aux_pexpr pes >>= fun pes' ->
    return_wrap (Ejump ((), sym, pes'))
```

#### `ocaml_frontend/rewriters/copy_propagation.ml` (after `Erun`, line 416)

```ocaml
| Ewhere (e, defs) ->
    Expr (annots, Ewhere (propagate env e,
      List.map (fun (sym_ty, params, body) -> (sym_ty, params, propagate env body)) defs))
| Ejump (a, lbl, pes) ->
    Expr (annots, Ejump (a, lbl, List.map pp pes))
```

#### `ocaml_frontend/pprinters/pp_core.ml` (after `Erun`, line 660)

```ocaml
| Ewhere (e, defs) ->
    pp_keyword "where" ^^^
    P.nest 2 (P.break 1 ^^ pp e) ^^^
    pp_control "with" ^^^
    P.nest 2 (P.break 1 ^^ comma_list (fun ((sym, bTy), sym_bTy_pes, body) ->
      pp_keyword "label" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^
      P.parens (comma_list (fun (sym, (bTy, _)) ->
        pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy
      ) sym_bTy_pes) ^^^
      pp_control "in" ^^^
      P.nest 2 (P.break 1 ^^ pp body)
    ) defs)
| Ejump (_, sym, pes) ->
    pp_keyword "jump" ^^^ pp_symbol sym ^^ P.parens (comma_list pp_pexpr pes)
```

#### `ocaml_frontend/milicore.ml` (after `Erun`, line 82)

```ocaml
| Ewhere (e, _defs) ->
    (* Labels from defs are pre-registered via m_collect_saves; just process body *)
    remove_save e
| Ejump _ -> expr
```

#### `ocaml_frontend/rewriters/core_peval.ml` (after `Erun`, line 379)

```ocaml
| Ewhere (e, defs) ->
    let defs' = List.map (fun (sym_ty, params, body) ->
      (sym_ty, params,
       if List.exists (fun (z, _) -> sym = z) params then body
       else subst_sym_expr2 sym z body)
    ) defs in
    Ewhere (subst_sym_expr2 sym z e, defs')
| Ejump (annot, lab_sym, pes) ->
    Ejump (annot, lab_sym, List.map (subst_sym_pexpr2 sym z) pes)
```

#### `ocaml_frontend/core_remove_unused_functions.ml`

The existing `| _ -> Traverse` catch-all already covers new cases — **no change needed**. (For correctness, `Ejump` should record a dep on its sym like `Erun` does, but that is a quality-of-life improvement, not required for the build.)

#### `ocaml_frontend/pprinters/pp_core_ast.ml` (after `Esave`, ~line 397)

```ocaml
| Ewhere (e, defs) ->
    Dnode (pp_ctor "Ewhere",
      self e :: List.map (fun ((sym, bTy), _, body) ->
        Dnode (pp_ctor "def" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy,
               [self body])
      ) defs)
| Ejump (_, sym, _) ->
    Dleaf (pp_ctor "Ejump" ^^^ pp_symbol sym)
```

Note: `milicore_label_inline.ml` already has `| _ -> Traverse` — **no change needed**.

---

### Phase 4 – Regeneration and build

```bash
make          # regenerates ocaml_frontend/generated/*.ml from .lem sources
dune build    # should now succeed (ignoring unrelated absint/coq errors)
```

---

## Verification

1. `dune build 2>&1 | grep "warning 8\|partial-match"` — should be empty (for cerberus targets)
2. Run the copy_prop tests (`tests/ci/0366–0373`) to verify no regressions
3. Check that a simple C file with a `while` loop runs through the elaboration pipeline without crashing

---

## Implementation sequence

### Workflow

After reviewing each change (but **before** committing): update the **Change log** section at the bottom of this document to note any deviations from the plan above.

---

### Commit 1 — Type fix + exhaustive stubs (build gate)

**Goal**: Fix the `Ewhere` type in `core.lem`, add minimal stub cases to every file that pattern-matches on `generic_expr_`, run `make` to regenerate, and verify `dune build` passes.

Every new case uses an error stub.
- `.lem`: `| Ewhere _ _ -> error "TODO <fn> Ewhere"` / `| Ejump _ _ _ -> error "TODO <fn> Ejump"`
- `.ml`: `| Ewhere _ -> failwith "TODO Ewhere"` / `| Ejump _ -> failwith "TODO Ejump"`

`frontend/model/core_sequentialise.lem` adds `import Utils` (unqualified import, not `open`); stubs use `Utils.error`.

**Files touched**:
- `frontend/model/core.lem` — type fix
- `frontend/model/core_sequentialise.lem` — add `import Utils`; stubs via `Utils.error`
- `frontend/model/core_aux.lem` — stubs (all 9 functions)
- `frontend/model/core_linking.lem` — stubs
- `frontend/model/core_indet.lem` — stubs
- `frontend/model/core_rewrite.lem` — stubs (all active functions)
- `frontend/model/core_rewrite2.lem` — stubs (alg_type fields added; fold_expr + default algebras are error stubs)
- `frontend/model/core_unstruct.lem` — stubs
- `frontend/model/core_typing.lem` — stubs
- `frontend/model/core_run_aux.lem` — stubs
- `frontend/model/core_run.lem` — stubs
- `frontend/model/core_reduction.lem` — stubs
- `parsers/core/core_parser.mly` — stubs (Commit 14; two match blocks)
- `backend/common/pipeline.ml` — stubs (Commit 15; `untype_expr`)
- `make` — regenerate `ocaml_frontend/generated/*.ml`
- All non-generated `.ml` files listed in Phase 3 — stubs

**Review checklist**:
- `dune build 2>&1 | grep -c "Error"` returns 0
- No `-w @8` partial-match warnings remain

---

### Commits 2–20 — Implementations (one file per commit)

Easy commits first; typing and execution last. Each commit: implement the
file, run `make && make install`, check the CI with `cd tests && ./run-ci.sh`,
log deviations.

| Commit | File | Notes |
|--------|------|-------|
| 2  | `frontend/model/core_sequentialise.lem` | Simple traversal |
| 3  | `frontend/model/core_unstruct.lem` | Simple pass-through |
| 4  | `frontend/model/core_indet.lem` | `indet_hack` traversal + `import_expr` errors |
| 5  | `frontend/model/core_rewrite.lem` | 8 active traversal functions |
| 6  | `frontend/model/core_rewrite2.lem` | `alg_type` fields + real `fold_expr` + real default algebras |
| 7  | `frontend/model/core_aux.lem` | All 9 functions (rows 1–9) |
| 8  | `ocaml_frontend/pprinters/pp_core.ml` | |
| 9  | `ocaml_frontend/pprinters/pp_core_ast.ml` | |
| 10 | `ocaml_frontend/rewriters/core_rewriter.ml` | |
| 11 | `ocaml_frontend/rewriters/copy_propagation.ml` | |
| 12 | `ocaml_frontend/rewriters/core_peval.ml` | |
| 13 | `ocaml_frontend/milicore.ml` | |
| 14 | `parsers/core/core_parser.mly` | `symbolify_expr` + `register_labels` |
| 15 | `backend/common/pipeline.ml` | `untype_expr` |
| 16 | `frontend/model/core_run_aux.lem` | 3 locations |
| 17 | `frontend/model/core_linking.lem` | Explain and ask |
| 18 | `frontend/model/core_run.lem` | Explain and ask |
| 19 | `frontend/model/core_reduction.lem` | Explain and ask |
| 20 | `frontend/model/core_typing.lem` | Explain and ask |

---

## Change log

*(Updated after each review, before each commit.)*

### Commit 1 deviations

- **`core_sequentialise.lem`**: `error` is not in scope by default (only `Core` is opened). Added `import Utils` (not `open`) so stubs can use `Utils.error`; the real implementation will be added in Commit 2.
- **`parsers/core/core_parser.mly`**: Not in the original plan; added as Commit 14. Has two match blocks on `generic_expr_`; added `| Ejump _ -> failwith "TODO Ejump"` + `| Ewhere _ -> failwith "TODO Ewhere"` to `symbolify_expr`, and added `| Ejump _ | Ewhere _` to the no-op group in `register_labels`.
- **`backend/common/pipeline.ml`**: Not in the original plan; added as Commit 15. Has an `untype_expr` function that pattern-matches exhaustively; added stubs there.
- **`core_aux.lem` rows 5–9** (`find_labeled_continuation`, `find_labeled_continuation2_aux`, `collect_labeled_continuations`, `collect_saves_aux`, `m_collect_saves_aux`): originally planned as trivial returns (correct by mutual-exclusivity invariant), now uniformly use error stubs like all other cases.

### Commit 2 (core_sequentialise.lem) deviations

- Removed the temporary `import Utils` added in Commit 1 (no longer needed once real implementation is in place; `error` is not called).

### Commit 3 (core_unstruct.lem) deviations

- `explode_expr` is dead code — `explode_file` is never called from the pipeline. The code also appears incomplete or potentially incorrect for `Esave` (whose arguments are always pointers to local variables, thus could be pointers to structs). Both new cases return `expr` unchanged, consistent with how `Esave` and `Erun` are handled.

### Commit 4 (core_indet.lem) — SKIPPED

- `core_indet.lem` is almost entirely commented out; only ~11 lines are live and `hackish_order` (the pipeline entry point) is a no-op stub. There is nothing meaningful to implement. The Commit 1 stubs already satisfy the exhaustiveness requirement. Skipped entirely; no implementation commit for this file.

### Commit 5 (core_rewrite.lem) deviations

- `remove_dead_aux` turned out to be dead code — it is commented out of `rewrite_expr` along with four other functions (`remove_skips`, `remove_unseqs`, `sequentialise_creates_kills`, `simpl_case`). Only `flatten_seqs` and `pure_propagation2` are actually called from the pipeline. All 8 functions were implemented regardless (the dead ones still need to compile), but the commit message documents which are live vs. dead.
- For `remove_dead_aux`, `Ejump` returns `Left expr` (like `Erun`) and `Ewhere` determines `Left`/`Right` based on its main expression `e`, with label bodies traversed in both branches.

### Commit 6 (core_rewrite2.lem) deviations

- The entire file is dead: `Core_rewrite2.rw_file` is commented out in `pipeline.ml` and nothing else calls `fold_expr`, `id_expr_alg`, or `pfp_expr_alg`. The plan did not note this; all three locations were implemented regardless (the file still needs to compile).
- The plan described adding `a_Ewhere` / `a_Ejump` fields to the `alg_type` record type. This was done correctly. The plan's code snippets for `id_expr_alg` and `pfp_expr_alg` used the name `pfp_expr_alg`; the actual names in the file match.

### Commit 7 (core_aux.lem) deviations

- Rows 5–9 (`find_labeled_continuation`, `find_labeled_continuation2_aux`, `collect_labeled_continuations`, `collect_saves_aux`, `m_collect_saves_aux`) were changed from error stubs (added in Commit 1) to proper error messages explaining that those cases should not be see in the programs where `Esave/Erun` exist. They could be implemented with the trivial "no match" returns originally planned if need be/required later.

### Commit 8 (pp_core.ml) deviations

- The plan's proposed layout (`pp_keyword "where" ^^^ ... pp_control "with" ^^^ ...`) was rejected after review. The final format was redesigned based on user feedback through several iterations:
  - `e` appears first (not inside a `where` wrapper)
  - The first label definition uses `where` as its keyword, indented on a new line (via `P.nest 2 (P.hardline ^^ ...)`)
  - Subsequent definitions use `and` (like OCaml's `let rec ... and ...`)
  - No surrounding `[` `]` brackets, no `pp_control "with"`, no `eff` keyword before the return type
- A local helper `pp_def` was introduced to avoid repeating the per-definition layout.

### Commit 9 (pp_core_ast.ml) deviations

- The plan said to add after `Esave` (~line 397). In practice, `pp_core_ast.ml` was not modified in Commit 1 (no stubs were added because the existing `| _ -> Dleaf (TODO_expr ...)` catch-all kept the file buildable). The new cases were added immediately before that catch-all.

### Commit 10 (core_rewriter.ml) deviations

- The plan's description implied `core_rewriter` was used by `copy_propagation.ml`; it is not. `core_rewriter.ml` is used only by `remove_unspecs.ml` and `core_peval.ml`. The commit message was corrected to reflect the actual callers.

### Commit 11 (copy_propagation.ml) deviations

- No deviations. `Ejump` maps `pp` (the local pexpr propagator) over its pexpr list, identical to the `Erun` case. `Ewhere` propagates through the main expression and each label body with `env` passed unchanged (label params shadow outer bindings but are not substituted by this pass).
