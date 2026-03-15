# Plan: mem2reg Analysis Phase

## Context

The `core_mem2reg.ml` pass is currently a stub (identity transform). This plan
implements **Phase 1 only**: the analysis that decides which Create-bound pointer
symbols are promotable. The transform phase comes later.

After this work, running `cerberus --sw mem2reg -d 3 file.c` will print which
pointer syms are promotable for each `Proc`, with no change to program semantics.

---

## High-level architectural decisions

**Single module, single concern.** Analysis and (future) transform stay in one
module because analysis results feed directly into the transform; splitting them
would require a callback or recursive-module declaration. Mutually recursive
functions (`collect_uses` / `sym_occurs_in_expr` / `sym_occurs_in_action`) are
kept together with `and` linkage.

**Plain recursive functions, not `Core_rewriter`.** `Core_rewriter` is designed
for tree rewrites. The analysis is a pure fold/query over the expression tree;
direct structural recursion is simpler and more readable.

**Conservative correctness over completeness.** Any use of a pointer symbol that
is not a plain Load0/Store0/Kill address argument immediately disqualifies it.
This keeps the analysis simple and safe, at the cost of missing some promotable
vars. `Esave` bodies are always conservative (loops may re-enter).

**Architectural flaw check:** No obvious flaws. The analysis is a read-only pass
that returns the file unchanged, so it cannot break existing semantics.

---

## Detailed design

### New files

| File | Purpose |
|---|---|
| `ocaml_frontend/rewriters/core_mem2reg.mli` | Public interface (written first) |
| `ocaml_frontend/rewriters/core_mem2reg.ml` | Implementation |
| `doc/history/2026-03-16_mem2reg-analysis.md` | Design doc archive |

### `core_mem2reg.mli`

The module exposes exactly one function. All internal types are hidden.

```ocaml
(** Promote function-local, non-address-taken C variables from
    Create/Store0/Load0/Kill sequences to pure Core let-bindings. *)

val transform_file : Symbol.sym Core.file -> Symbol.sym Core.file
```

(`Core.file` is `type 'a file = (unit, 'a) generic_file` — the untyped file
that `core_passes` in `pipeline.ml` passes around.)

---

### Internal type `use`

```ocaml
type use =
  | Use_load    (* Load0(_, PEsym ptr, _) — address argument *)
  | Use_store   (* Store0(_, _, PEsym ptr, _, _) — address argument *)
  | Use_kill    (* Kill(_, PEsym ptr) *)
  | Use_other   (* any other occurrence *)
```

`use_is_promotable` replaces any `u <> Use_other` guards (avoids generic equality):

```ocaml
let use_is_promotable = function
  | Use_load | Use_store | Use_kill -> true
  | Use_other -> false
```

### Occurrence helpers

Three mutually recursive functions: `sym_occurs_in_pexpr`, `sym_occurs_in_expr`,
`sym_occurs_in_action`. Return `bool`: does `PEsym sym` appear anywhere in this
term? Used as the conservative fallback.

### `classify_action`

Returns `use list` for a given sym in one action. Load0/Store0/Kill are
classified precisely; everything else uses `sym_occurs_in_action` as fallback.

### `collect_uses`

Structural recursion over `expr`. `Esave` is always conservative (loop bodies).

### `collect_creates`

Finds all `Esseq`-bound `Create(PrefSource _)` syms. `PrefSource` required —
excludes dynamic `Alloc0` and `CreateReadOnly`.

### `find_promotable`

Calls `collect_creates` and filters by `is_promotable`. Emits debug at level 3.

### `transform_file`

Analysis phase only. Iterates over `file.funs` bindings for debug output using
`Pmap.bindings_list`, then returns the file structurally unchanged.

---

## Verification

```sh
# 1. Build and install
make && make install

# 2. Simple case — one promotable var
cerberus --sw mem2reg -d 3 tests/ci/0341-mem2reg_simple.c 2>&1 | grep mem2reg
# Expected: "[mem2reg] foo: 1 promotable: [ptr_x_NNN]"

# 3. Address-taken — zero promotable
cerberus --sw mem2reg -d 3 tests/ci/0346-mem2reg_no_promote_address.c 2>&1 | grep mem2reg
# Expected: "[mem2reg] ...: 0 promotable: []"

# 4. No-switch case — no output
cerberus tests/ci/0341-mem2reg_simple.c 2>&1 | grep mem2reg
# Expected: (empty)

# 5. Mixed — partial promotion
cerberus --sw mem2reg -d 3 tests/ci/0350-mem2reg_mixed.c 2>&1 | grep mem2reg
# Expected: some syms listed, some not
```
