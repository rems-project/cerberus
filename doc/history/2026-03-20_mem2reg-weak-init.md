# Plan: Refactor `check_definitely_init` to use `write_kind`

## Context

`check_definitely_init` currently returns `bool * bool` where the second bool means
"sym is definitely initialized after this expression."  This conflates two distinct
notions of initialization that matter for correctness:

- **Strong** (`Paction Pos` store, or Esseq-sequenced write): the store is committed
  before any continuation that follows with `Esseq`.
- **Weak** (`Paction Neg` store in an `Ewseq` bound): the store is *unsequenced* w.r.t.
  the `Ewseq` continuation, so the continuation cannot rely on it.

A `Load0` or `SeqRMW` is only safe if the variable was **strongly** initialized.
The existing `bool` cannot express this distinction, causing the analysis to be
either unsound (if Weak is treated as Strong) or overly conservative (if Weak is
treated as No_write).

---

## New module

```ocaml
module Write_kind = struct
  type t = No_write | Weak | Strong

  (* || = join: least upper bound — goes up the lattice *)
  let (||) a b = match a, b with
    | No_write, x | x, No_write -> x
    | Strong,   _ | _, Strong   -> Strong
    | Weak,     Weak             -> Weak

  (* && = meet: greatest lower bound — goes down the lattice *)
  let (&&) a b = match a, b with
    | Strong,   x | x, Strong   -> x
    | No_write, _ | _, No_write -> No_write
    | Weak,     Weak             -> Weak

  let of_bool = function true -> Strong | false -> No_write

  let is_strong   = function Strong   -> true | _ -> false
  let is_weak     = function Weak     -> true | _ -> false
  let is_no_write = function No_write -> true | _ -> false
end
```

Lattice: `No_write < Weak < Strong`. `(||)` is join (goes up); `(&&)` is meet (goes down).

---

## Signature change

The `already_init` parameter is renamed to `strongly_init` (it remains a `bool`).
It is only ever `true` (sym is strongly initialized on entry) or `false`.
When converting a `Write_kind.t` result to a `bool` to pass as `strongly_init`
to a sub-expression, use `Write_kind.is_strong`, `is_weak`, or `is_no_write`
as appropriate — never a generic `to_bool`.

```ocaml
val check_definitely_init :
  (bool * Write_kind.t) memo_save_info ->
  Symbol.sym ->
  bool ->                    (* strongly_init: sym is strongly initialized on entry *)
  (_, _, _) generic_expr ->
  bool * Write_kind.t        (* (safe, init_after) *)
```

The `init_memo` type annotation changes from `(bool * bool) memo_save_info`
to `(bool * Write_kind.t) memo_save_info`.

---

## Case-by-case rules

### Leaf actions

`strongly_init` is a `bool`. Where the existing code returned `already_init` as
`init_after`, now use `Write_kind.of_bool strongly_init`.

| Action | Condition | Returns |
|--------|-----------|---------|
| `Store0 (Paction Pos, _, addr, _, _)` when `is_pesym sym addr` | — | `(true, Write_kind.Strong)` |
| `Store0 (Paction Neg, _, addr, _, _)` when `is_pesym sym addr` | — | `(true, Write_kind.Weak)` |
| `Load0 (_, addr, _)` when `is_pesym sym addr` | — | `(strongly_init, Write_kind.of_bool strongly_init)` |
| `Kill (_, addr)` when `is_pesym sym addr` | — | `(true, Write_kind.No_write)` |
| `SeqRMW (_, _, addr, _, _)` when `is_pesym sym addr` | — | `(strongly_init, Write_kind.Strong)` |
| anything else | — | `(true, Write_kind.of_bool strongly_init)` |

### `Esseq(_, e1, e2)` — strong sequencing

Strong sequencing promotes Weak writes to Strong before threading into e2:
a Neg store that is strongly sequenced IS committed before e2.
Use `not (Write_kind.is_no_write ia1)` to convert: any initialization (Weak or
Strong) becomes `true`; No_write stays `false`.

```ocaml
let (s1, ia1) = check_definitely_init memo sym strongly_init e1 in
let (s2, ia2) = check_definitely_init memo sym (not (Write_kind.is_no_write ia1)) e2 in
(s1 && s2, ia2)
```

### `Ewseq(_, e1, e2)` — weak sequencing

Only a Strong write in e1 is sequenced before e2. Weak writes are unsequenced, so
e2 sees only `strongly_init`.

```ocaml
let (s1, ia1) = check_definitely_init memo sym strongly_init e1 in
let (s2, ia2) = check_definitely_init memo sym (Write_kind.is_strong ia1 || strongly_init) e2 in
(s1 && s2, Write_kind.(ia1 || ia2))
```

### `Eunseq arms` — unsequenced

All arms see `strongly_init`. `init_after` is the **meet** of all arms (all paths
must initialize, and the weakest strength wins).

```ocaml
let results = List.map (check_definitely_init memo sym strongly_init) arms in
let safe    = List.for_all (fun (s, _) -> s) results in
let ia      = List.fold_left Write_kind.(fun acc (_, k) -> acc && k) Write_kind.Strong results in
(safe, ia)
```

### `Eif(_, et, ef)` and `Ecase(_, arms)` — conditional

Both branches see `strongly_init`. `init_after` is the **meet** across branches.

```ocaml
(* Eif *)
let (st, iat) = check_definitely_init memo sym strongly_init et in
let (sf, iaf) = check_definitely_init memo sym strongly_init ef in
(st && sf, Write_kind.(iat && iaf))

(* Ecase: fold Write_kind.(&&) over all arm results, starting from Write_kind.Strong *)
```

### `Esave` — loop header

Sentinel changes from `(true, true)` to `(true, Write_kind.Strong)` (same reasoning;
Strong is the over-approximating choice for the fixpoint sentinel).

Safety and init-after at the Esave call site:

```ocaml
let safe      = strongly_init || safe_uninit in
let init_after = Write_kind.(of_bool strongly_init || inits_param) in
(safe, init_after)
```

### `Erun` — loop back-edge (terminal)

```ocaml
let safe = strongly_init || safe_uninit in
(safe, Write_kind.Strong)   (* continuation unreachable; Strong is vacuously correct *)
```

### `Elet / Ebound / Eannot` — transparent

```ocaml
check_definitely_init memo sym strongly_init inner_e
```

### Catch-all

```ocaml
(true, Write_kind.of_bool strongly_init)
```

---

## Call site changes

In `find_promotable`:

```ocaml
(* init_memo type annotation *)
let init_memo : (bool * Write_kind.t) memo_save_info = ...

(* initial call: sym is not strongly initialized at function entry *)
fst (check_definitely_init init_memo s false body)
```

---

## Critical files

- `ocaml_frontend/rewriters/core_mem2reg.ml` — all changes live here

---

## Verification

```sh
make && make install
cerberus --sw mem2reg file.c      # check a local C file
cd tests && USE_OPAM='' bash run-ci.sh
```

---

## Rigorous Testing of Write_kind

### Background: what the old vs new analysis does differently

The only behavioural change relative to the old `bool`-based analysis is in the
`Ewseq` case:

| Scenario | Old (bool) | New (Write_kind) |
|---|---|---|
| `Store0(Paction Pos)` in Ewseq e1, `Load0` in e2 | e2 sees `already_init` (false) → **NOT safe** → not promoted | e2 sees `is_strong Strong = true` → **safe** → promoted |
| `Store0(Paction Neg)` in Ewseq e1, `Load0` in e2 | e2 sees `already_init` (false) → not safe | e2 sees `is_strong Weak = false` → not safe (correct) |
| Any store in Esseq e1, `Load0` in e2 | e2 sees `ia1 = true` → safe | e2 sees `not (is_no_write ?) = true` → same |

The canonical C construct that generates `Store0(Paction Pos)` inside `Ewseq e1`
followed by `Load0` in `e2` is a **compound literal**: `(T){ expr }` creates an
anonymous temporary whose initialization store appears as `Ewseq(_, Store0(Pos,
ptr_tmp, val), Load0(ptr_tmp))` in the Core IR.

### New test: `0365-mem2reg_compound_lit.c`

```c
/* Tests that a local variable initialised via a compound literal is
   promotable.  The Core IR for (int){ 42 } contains:
       Ewseq(_, Store0(Paction Pos, ptr_tmp, 42), Load0(ptr_tmp))
   Under the old bool-based analysis, Load0 in the Ewseq e2 saw
   `already_init = false` (init in e1 was not forwarded) → NOT promotable.
   Under the new Write_kind analysis, Strong from e1 propagates to e2 → IS
   promotable.  This is the "strong write in weak sequence" test case. */
int main(void) {
    int x = (int){ 42 };
    return x;
}
```

- **Expected output**: `Defined {value: "Specified(42)", stdout: "", stderr: "", blocked: "false"}`
- **Phase 2 stub count**: determined empirically after implementation (see below)
- **Phase 2 fully-working target**: 0 (both compound-literal temp and x are promotable)

### Steps to add the test

1. Write `tests/ci/0365-mem2reg_compound_lit.c` with the content above.
2. Write `tests/ci/expected/0365-mem2reg_compound_lit.expected` with the expected output.
3. Determine the phase 2 stub create count:
   ```sh
   cerberus --nolibc --pp core --sw mem2reg tests/ci/0365-mem2reg_compound_lit.c \
     | grep -c 'create('
   ```
4. Add to `elim_expected` in `tests/run-mem2reg-phase2.sh`:
   ```bash
   [0365-mem2reg_compound_lit.c]=N   # N from step 3
   ```
5. Update the fully-working-pass comment at the top of `run-mem2reg-phase2.sh`
   to include `0365=0`.

### Write the plan to `doc/history/`

As per `CLAUDE.md`, copy this plan to:
```
doc/history/2026-03-20_write-kind-refactor.md
```

### Full verification sequence

```sh
make && make install

# Determine create count for new test
cerberus --nolibc --pp core --sw mem2reg \
  tests/ci/0365-mem2reg_compound_lit.c | grep -c 'create('

# Run both mem2reg phases
cd tests
USE_OPAM='' bash run-mem2reg-phase1.sh
USE_OPAM='' bash run-mem2reg-phase2.sh
```
