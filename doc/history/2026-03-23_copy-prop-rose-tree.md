# Copy Propagation: Rose-tree tail, tuple patterns, Eunseq RHS

**Date:** 2026-03-23
**File:** `ocaml_frontend/rewriters/copy_propagation.ml`

---

## Motivation

The previous `tail_pexpr` (returning `pexpr option`) returned `None` for
`Eunseq`, so copy-propagation could not extract bindings when:

- the pattern was a tuple (`CaseCtor(Ctuple, pats)`), and
- the RHS was `Eunseq(es)` — the standard Core encoding of C comparison
  operators, function-pointer loads, and other unsequenced expressions.

For example, in the Core of `do_uninit.c`:

```
let weak (a_516, a_517) = unseq(load(x), pure(Specified(0))) in
case (a_516, a_517) of ...
```

`a_517` was always 0, but the pass could not propagate that constant into the
`case` because the pattern was a tuple and the RHS was `Eunseq`.

---

## Design

### `pexpr_tree`

A rose tree that mirrors the `Eunseq` / `CaseCtor(Ctuple)` nesting:

```ocaml
type pexpr_tree =
  | Leaf of pexpr option   (* known/unknown pure expression *)
  | Node of pexpr_tree list (* Eunseq with per-arm subtrees *)
```

### `tail_pexpr_acc` / `tail_pexpr`

Return type changed from `pexpr option` to `pexpr_tree`.  The `Eunseq` case
now builds a `Node`:

```ocaml
| Eunseq es -> Node (List.map (tail_pexpr_acc binders) es)
```

All other cases change `Some`/`None` to `Leaf(Some ...)`/`Leaf None`.

### `match_pat_tree`

New function that walks a pattern and a `pexpr_tree` in lock-step, returning
`(bindings, new_pattern)`:

| Pattern            | Tree                      | Result                            |
|--------------------|---------------------------|-----------------------------------|
| `CaseBase(Some s)` | `Leaf(Some pe)`           | `s → pe`, pattern wildcarded      |
| `CaseBase(Some s)` | `Leaf None` or `Node _`   | no extraction                     |
| `CaseBase(None)`   | any                       | no extraction                     |
| `CaseCtor(Ctuple)` | `Node trees` (same arity) | recurse element-wise              |
| `CaseCtor(Ctuple)` | `Leaf(Some PEctor(Ctuple, pes))` (same arity) | decompose element-wise |
| anything else      | anything else             | no extraction (fallthrough)       |

The `Leaf(Some PEctor(Ctuple,...))` case handles `Elet` with a pure-tuple RHS.

### Updated `propagate_expr` catch-alls

The three catch-all arms for `Ewseq`, `Esseq`, and `Elet` now use
`match_pat_tree` for partial tuple extraction:

```ocaml
| Ewseq (pat, e1, body) ->
    let e1' = propagate_expr env e1 in
    let (bindings, new_pat) = match_pat_tree pat (tail_pexpr e1') in
    let env' = extend_env_list env bindings in
    Expr (annots, Ewseq (new_pat, e1', propagate_expr env' body))
```

(Symmetric for `Esseq`. For `Elet`, `Leaf(Some pe1')` is passed instead of
`tail_pexpr e1'`.)

The specific `CaseBase(Some alias)` arms for `Ewseq`/`Esseq` (which fire
first) are updated to match against `Leaf(Some pe_tail)` / `_` instead of
`Some pe_tail` / `None`.

---

## Correctness notes

- `pexpr_safe` is unchanged; it still guards against hoisting expressions whose
  free variables are locally bound along the chain.
- `binders_of_pat` is unchanged; it handles both `CaseBase` and `CaseCtor`.
- Extraction is **partial**: positions where the tree gives `Leaf None` retain
  their original names.
- The binding node is always preserved (pattern element replaced by wildcard,
  not dropped), so source-location annotations are not lost.
- `Eunseq` introduces no new binders; the accumulator is unchanged when
  recursing into `Eunseq` arms.

---

## Example walkthrough (`do_uninit.c`)

Input:
```
Ewseq(CaseCtor(Ctuple, [CaseBase(Some a_516); CaseBase(Some a_517)]),
      Eunseq([e_load, Epure(Specified(0))]),
      body)
```

1. `e1' = propagate_expr env (Eunseq([e_load, Epure(Specified(0))]))`
2. `tail_pexpr e1' = Node([Leaf None, Leaf(Some Specified(0))])`
3. `match_pat_tree (a_516, a_517) (Node([Leaf None, Leaf(Some ...)]))`
   → `bindings = [(a_517, Specified(0))]`, `new_pat = (a_516, _)`
4. `env' = env ∪ {a_517 → Specified(0)}`
5. `propagate_expr env' body` → `PEsym a_517` replaced by `Specified(0)`

---

## Post-implementation addendum

During testing, a Core typechecker bug was exposed: the typechecker incorrectly
rejected certain `loaded object` / `loaded pointer` expressions that are
semantically equivalent. This was fixed in the typechecker independently;
the copy-propagation pass itself is correct.

All 188 CI tests pass with `--sw copy_prop`, and all 188 pass without the
switch (full CI suite).
