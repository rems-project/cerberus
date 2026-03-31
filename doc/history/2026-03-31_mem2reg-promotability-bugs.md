# Plan: Fix Two mem2reg Promotability Bugs

## Context

Eight tests in `run-mem2reg-phase2.sh` show wrong promotable-symbol sets.
Investigation of post-copy_prop Core IR reveals two independent bugs in
`ocaml_frontend/rewriters/core_mem2reg.ml`.

---

## Bug 1 — `is_init_env` discards outer `env` when Esave body is transparent

### Root cause

`is_init_env` is called after analysing an Esave body via `save_param_needs_init`.
When `needs_init = false` (body never reads sym before writing, or never touches sym
at all) it unconditionally returns `param_env`:

```ocaml
let is_init_env needs_init ~param_env ~env =
  if needs_init then ...
  else
    param_env   (* BUG: always returns param_env, ignoring env *)
```

`save_param_needs_init` always analyses the body starting from `Uninit`.  If the
body never touches sym (e.g. `x` in `save while_513(x:=x, i:=i)` where the loop
only modifies `i`), `param_env = Uninit`.  The outer `env` may be `Init` (x was
stored before the loop), but `is_init_env false ~env=Init ~param_env=Uninit`
returns `Uninit`, erasing the initialisation.

Any subsequent Load of sym then sees `env = Uninit` and raises `Load_from_uninit`,
causing `is_promotable` to return false.

The same bug fires for the auxiliary `save continue_NNN` / `save break_NNN` Esaves
whose bodies are `pure(Unit)` — they also leave `param_env = Uninit`, which
overwrites `env = Init` for every sym threaded through them.

### Fix

When `needs_init = false` and `param_env = Uninit` (body didn't change sym), the
outer state persists.  When `param_env = Init | Killed` the body did change sym,
so `param_env` is authoritative:

```ocaml
let is_init_env needs_init ~param_env ~env =
  if needs_init then
    (match env with
    | Killed -> raise Not_sequentialisable
    | Uninit -> raise Load_from_uninit
    | Init -> param_env)
  else
    (match param_env with
     | Uninit -> env            (* body didn't alter sym; outer state persists *)
     | Init | Killed -> param_env)
```

### Affected tests

| Test | Missed sym | Why |
|---|---|---|
| 0345 | `x` | x not used in while/break bodies → param_env=Uninit, outer Init discarded |
| 0348 | `x` | same; x IS used in loop body but continue/break bodies still fire the bug |
| 0361 | `x` | `save continue_510` body is `pure(Unit)` → resets env to Uninit mid-analysis |

---

## Bug 2 — `collect_creates` misses `PrefCompoundLiteral`

### Root cause

`collect_creates` only matches `PrefSource` (and conditionally `PrefFunArg`):

```ocaml
| Esseq (
    Pattern (_, CaseBase (Some ptr_sym, _)),
    Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefSource _))))),
    body
  ) -> ptr_sym :: collect_creates ~also_fun_args body
```

Compound-literal temporaries (`(int){42}`) are created with `Symbol.PrefCompoundLiteral`.
They are `let strong` (Esseq) bindings that appear in the function body, are only
stored/loaded/killed via direct pointer use, and are otherwise entirely promotable.
They are invisible to the analysis and never considered as candidates.

### Fix

Add `PrefCompoundLiteral` to the pattern (using an or-pattern):

```ocaml
| Esseq (
    Pattern (_, CaseBase (Some ptr_sym, _)),
    Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _,
        (Symbol.PrefSource _ | Symbol.PrefCompoundLiteral _)))))),
    body
  ) -> ptr_sym :: collect_creates ~also_fun_args body
```

### Affected tests

| Test | Missed sym | Why |
|---|---|---|
| 0365 | `a_508` (compound lit temp for `(int){42}`) | PrefCompoundLiteral not matched |

---

## Tests 0346 / 0347 / 0350 / 0362

Post-copy_prop Core IR analysis confirms the current analysis is **correct** for
these tests.  Their expected values in the test script are already right and will
not change after the fixes.  They appear in the user's list possibly because all
eight were flagged together for review.

---

## Critical files

- `ocaml_frontend/rewriters/core_mem2reg.ml` — two changes:
  1. `is_init_env` function (~line 388)
  2. `collect_creates` function (~line 278)
- `tests/run-mem2reg-phase2.sh` — regenerate expected values with `--generate`

---

## Implementation steps

1. Fix `is_init_env` (replace the `else param_env` arm).
2. Fix `collect_creates` (add `PrefCompoundLiteral` or-pattern).
3. Build: `make && make install`.
4. Regenerate: `USE_OPAM='' bash tests/run-mem2reg-phase2.sh --generate`.
5. Paste updated `promotable_expected` into `run-mem2reg-phase2.sh`.
6. Verify: `USE_OPAM='' bash tests/run-mem2reg.sh`.
7. Copy plan to `doc/history/2026-03-31_mem2reg-promotability-bugs.md`.

---

## Expected new promotable sets after fixes

| Test | Before | After |
|---|---|---|
| 0345 | `[i_505]` | `[x_504, i_505]` |
| 0348 | `[i_505]` | `[x_504, i_505]` |
| 0361 | `[]` | `[x_504]` |
| 0365 | `[x_504]` | `[a_508, x_504]` |
| 0346/0347/0350/0362 | unchanged | unchanged |

---

## Verification

```bash
make && make install
cd tests
USE_OPAM='' bash run-mem2reg-phase2.sh --generate   # inspect output
USE_OPAM='' bash run-mem2reg.sh                      # both phases pass
USE_OPAM='' bash run-ci.sh                           # full CI unbroken
```
