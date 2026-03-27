# Plan: Unify promotability analyses into `sequentialisable`

## Context

`core_mem2reg.ml` previously ran three separate analyses on a procedure body to decide
if a Create-bound pointer `sym` is promotable:

1. `check_definitely_init` — checks that no load-before-store occurs on any path and
   tracks `Write_kind` (No_write / Weak / Strong) across branches.
2. `expr_writes_sym` — helper for (3): predicate, "does this sub-expr contain a Store0
   to sym?".
3. `no_mixed_unseq_uses` — checks that if sym appears in a write arm of an `Eunseq`,
   no other arm also mentions sym (would hide a sequencing violation).

All three traverse the same IR and share overlapping logic.  They are collapsed into
one abstract-interpretation function `sequentialisable` that returns the event sequence
the expression performs on `sym` together with the env (init state) of `sym` after
the expression.

---

## New types

### `module Mem_event`

```ocaml
module Mem_event = struct
  type t = Pos_store | Neg_store | Load | Kill
end
```

No pexpr payload.  Values are tracked directly in `env`.

### `env`

```ocaml
type env = Uninit | Init of pexpr | DelayedInit of pexpr | Killed
```

- `Uninit` — no store observed yet on this path.
- `Init pe` — sym was last stored with committed value `pe`.
- `DelayedInit pe` — sym was stored (Neg polarity, Ewseq e1) but not yet committed;
  subsequent e2 must not observe this.
- `Killed` — sym's allocation was freed.

### Exceptions

```ocaml
exception Not_sequentialisable
exception Load_from_uninit
```

`Not_sequentialisable` is raised when:
- Any action on sym is encountered with `env = DelayedInit _`.
- An `Eunseq` has ≥2 arms with events on sym, or mixed read/write arms.

`Load_from_uninit` is raised specifically when `Load0` or `SeqRMW` encounters
`env = Uninit`.  It is caught by `esave_needs_init` to detect that the Esave body
needs sym initialized on entry; if the outer env is `Init _` this is recoverable.

---

## `sequentialisable` signature

```ocaml
val sequentialisable :
  seq_memo ->
  Symbol.sym -> env ->
  (unit, unit, Symbol.sym) generic_expr ->
  (Mem_event.t list * env) option
```

- `None` — the expression's control flow ends in an `Erun` on all paths (vacuously OK).
- `Some (events, env')` — events observed on sym and the env after the expression.
- Raises `Not_sequentialisable` on any conflict.

Uses `let ( let* ) = Option.bind`.

---

## Memoization: `seq_memo`

Reuses the polymorphic `'a esave_memo_entry` / `'a memo_save_info` machinery with
`'a = bool * (Mem_event.t list * env) option`:

```ocaml
(* seq_memo_result: (init_needed, body_result)
     init_needed – false: body self-initialises; true: needs Init _ on entry
     body_result – None while analysis in progress (sentinel) or when all body
                   paths end in Erun; Some (ev, env') after a non-Erun result *)
type seq_memo_result = bool * (Mem_event.t list * env) option
type seq_memo = seq_memo_result memo_save_info
```

Built the same way as `init_memo` was:

```ocaml
let seq_memo : seq_memo =
  Pmap.map (fun { params; body; _ } ->
    { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) use_memo
```

---

## Case-by-case design

### `Eaction`

All actions on sym first check: if `env = DelayedInit _`, raise `Not_sequentialisable`.

| Action | Condition | Events | `env'` |
|---|---|---|---|
| `Store0(_, _, addr, val_pe, _)` Pos | `is_pesym sym addr` | `[Pos_store]` | `Init val_pe` |
| `Store0(_, _, addr, val_pe, _)` Neg | `is_pesym sym addr` | `[Neg_store]` | `DelayedInit val_pe` |
| `Load0(_, addr, _)` | `is_pesym sym addr`, `env = Init _` | `[Load]` | `env` |
| `Load0` | `is_pesym sym addr`, `env = Uninit` | raise `Load_from_uninit` | — |
| `Load0` | `is_pesym sym addr`, other non-Init env | raise `Not_sequentialisable` | — |
| `Kill(_, addr)` | `is_pesym sym addr` | `[Kill]` | `Killed` |
| `SeqRMW(_, _, addr, tmp_sym, upd_pe)` | `is_pesym sym addr`, `env = Init pe` | `[Load; Pos_store]` | `Init (subst tmp_sym pe upd_pe)` |
| `SeqRMW` | `is_pesym sym addr`, `env = Uninit` | raise `Load_from_uninit` | — |
| `SeqRMW` | `is_pesym sym addr`, other non-Init env | raise `Not_sequentialisable` | — |
| other | — | `[]` | `env` |

### `Esseq (_, e1, e2)`

Strong sequencing commits any store in e1 before e2 begins, so a `DelayedInit`
result from e1 is promoted to `Init` for e2.

```ocaml
let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
let env1' = match env1 with DelayedInit pe -> Init pe | _ -> env1 in
let* (ev2, env2) = sequentialisable seq_memo sym env1' e2 in
Some (ev1 @ ev2, env2)
```

### `Ewseq (_, e1, e2)`

If e1 produces `DelayedInit`, any subsequent action on sym in e2 will raise
`Not_sequentialisable` naturally (since all actions check `DelayedInit` first).
We thread `env1` directly into e2 without any special-casing.

```ocaml
let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
let* (ev2, env2) = sequentialisable seq_memo sym env1 e2 in
Some (ev1 @ ev2, env2)
```

### `Eif` and `Ecase`

Pass the same incoming `env` into each branch; combine results by checking that events
agree and envs are compatible.

`combine_branches pe_cond r1 r2`:
- Both `None` → `None`
- One `None`, other `Some result` → `Some result`
- Both `Some (ev1, env1)` and `Some (ev2, env2)`:
  - Events are appended (over-approximation).
  - Envs: `Uninit+Uninit→Uninit`, `Killed+Killed→Killed`, `Init/Init→Init(PEif)`,
    `Delayed/Delayed→Delayed(PEif)`, `Init/Delayed→Delayed(PEif)`,
    otherwise raise.
  - Return `Some (ev1, combined_env)`

### `Eunseq arms`

Collect arms with events; if all reads → OK; if exactly one write arm → OK; else raise.

### `Esave` and `Erun`

Shared helper `esave_needs_init seq_memo sym env label_sym param_sym`:
- Looks up `(label_sym, param_sym)` in memo.
- If `init_needed=true` and outer `env ≠ Init _`: raise `Load_from_uninit`.
- If not memoised: write sentinel `(false, None)`, run with `Uninit`, catch
  `Load_from_uninit`, re-run with outer `env` and mark `init_needed=true`.

---

## Removals

| Removed | Replaced by |
|---|---|
| `module Write_kind` | `env` + `Mem_event` |
| `check_definitely_init` | `sequentialisable` |
| `expr_writes_sym` | events-list inspection |
| `no_mixed_unseq_uses` | `Eunseq` case of `sequentialisable` |
| `init_memo` in `find_promotable` | `seq_memo` |

---

## Post-implementation addendum

### Implementation notes

**`sym_occurs_in_expr` removal**: `sym_occurs_in_expr` and `sym_occurs_in_action`
were previously defined as a mutually-recursive `and` chain with
`sym_occurs_in_pexpr`.  After removing `no_mixed_unseq_uses`, neither is referenced
by any other function in the file (only `sym_occurs_in_action` is still needed by
`classify_action`).  Removed `sym_occurs_in_expr` entirely and detached
`sym_occurs_in_action` from the `and` chain, making it a standalone `let`.

**`combine_branches` signature**: needs `pe_cond : pexpr` to construct `PEif` nodes
when combining `Init`/`DelayedInit` envs from branches.  For `Ecase`, the case
discriminant `pe` is used as condition for all combination steps — semantically
approximate but fine for analysis (only constructor of env matters).

**`Ewseq` precision**: the new design is slightly more conservative than
`check_definitely_init` for one pattern: if sym is `Init` before `Ewseq e1`, and e1
does a Neg/weak store, the old code kept `strongly_init=true` for e2.  The new code
threads `DelayedInit` into e2, and any action there raises `Not_sequentialisable`.
This pattern does not appear in elaborated C code for normal stack variables, so no
test regression was observed.

### Test results (all passing)

- `run-mem2reg-phase1.sh`: 188 passed, 0 failed
- `run-mem2reg-phase2.sh`: 21 passed, 0 failed
- `run-copy-prop-phase1.sh`: 208 passed, 0 failed
- `run-copy-prop-phase2.sh`: 9 passed, 0 failed
- `run-ci.sh`: 208 passed, 0 failed
