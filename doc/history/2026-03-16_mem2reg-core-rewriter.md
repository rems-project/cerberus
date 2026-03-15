# Discussion: Should mem2reg use `core_rewriter`?

## What `core_rewriter` provides

`core_rewriter` is a transformation functor `Rewriter(Eff: Monad)` that provides a
visitor pattern with three mutually-recursive rewriters — `rw_pexpr`, `rw_action`,
`rw_expr` — each returning one of:

```
Unchanged | Update v | Traverse | PostTraverseAction f
| DoChildrenPost f | ChangeDoChildrenPost(v, f)
```

The `Eff` monad parameter threads arbitrary state through the traversal.

---

## Analysis phase — do NOT use `core_rewriter`

The analysis phase consists of four functions: `collect_creates`, `collect_uses`,
`check_definitely_init`, and `no_mixed_unseq_uses`.  None of them fit the
`core_rewriter` model.

### `collect_creates`

A simple 28-line recursive descent accumulating a symbol list.
Rewriting it with `core_rewriter` would require instantiating the functor, defining
three rewriter records for a single pattern, and wiring `PostTraverseAction`
callbacks.  Net result: more code, more indirection, no gain.

### `collect_uses`

A **context-sensitive fold**, not a transformation.  It classifies uses
differently depending on where in the AST the symbol appears:

- Inside `Esave` → always `Use_other` (requires a downward context flag)
- As the address argument of `Load0`/`Store0`/`Kill`/`SeqRMW` → `classify_action`
- Anywhere else → `Use_other`

`core_rewriter` has no mechanism to:
- Pass a "we are inside `Esave`" context flag downward
- Distinguish *which* argument position a pexpr occupies within an action
- Return a classification rather than a transformed node

Forcing this in would require the `Eff` monad to carry a context stack *and* an
accumulated use list, with per-constructor `PostTraverseAction` hooks — strictly
more complex than the current 47-line hand-rolled traversal.

### `check_definitely_init`

A **two-valued downward-and-upward pass** that returns `(safe, init_after)`:

- `safe`: no load-before-store on any syntactic path
- `init_after`: on ALL syntactic paths, at least one store has occurred

It carries `already_init : bool` **downward** — a context value that changes as
the traversal descends through sequential nodes.  `core_rewriter` threads monadic
state sequentially through children but has no concept of a *downward* context; it
cannot model "pass `already_init = true` into the continuation after seeing a
store".

Two cases require non-uniform child handling that `core_rewriter` cannot express:

- **`Ewseq`**: the init-after result of `e1` is propagated *into* `e1`'s own
  subtree but **not** into `e2` (negative actions in `e1` are not sequenced before
  `e2`).  A uniform left-to-right state thread would incorrectly propagate `ia1`
  to `e2`.
- **`Eunseq`**: each arm is visited with the *same* `already_init` (no arm's
  result is visible to any sibling).  `safe` and `init_after` are both
  all-arms-must-agree conjunctions.

Additionally the function returns `(bool * bool)`, not a transformed node — there
is no natural way to encode that in `core_rewriter`'s result type.

### `no_mixed_unseq_uses`

A **collective-arms predicate** over `Eunseq` nodes.  For each `Eunseq` it asks:
*does any arm write `sym` while ≥ 2 arms mention `sym`?*  This is a conflict check
across all sibling arms simultaneously.

`core_rewriter` visits children one at a time and cannot gather information about
all siblings before deciding whether the parent node is safe.  Implementing this
check would require a `PostTraverseAction` hook that re-examines all arms after the
fact — but the rewriter has already dispatched to each arm independently, so the
sibling set is no longer available.

Like `check_definitely_init`, the function returns a `bool`, not a transformed
node.

**Conclusion: keep all four analysis functions hand-rolled.**

---

## Transformation phase — also do NOT use `core_rewriter`

For straight-line code, threading an `env : (sym * sym) list` through the `Eff`
state monad and returning `Update` would work.  But mem2reg must correctly handle
**branches** (`Eif`, `Ecase`):

When a promotable variable is written inside one or both branches, the algorithm
must:

1. **Fork** the env — transform each branch independently with the *same* env snapshot.
2. Compute `written_vars` across branches.
3. Mint fresh `phi_sym` per written variable.
4. Restructure the outer `Esseq` node so the `Eif` result becomes a tuple
   `(unit × val_ty_1 × … × val_ty_n)`; destructure the tuple and extend the env
   with `ptr_x ↦ phi_sym_x` before transforming the continuation.

`core_rewriter` threads state **sequentially** through children — it cannot fork
state for parallel branches.  Handling branching would require manually calling the
rewriter recursively inside a `rw_expr` handler for `Eif`/`Ecase`, which defeats
the purpose of using the framework at all.

**Conclusion: Phase 2 is also hand-rolled**, using an explicit recursive
`transform_expr env promotable expr` function.
