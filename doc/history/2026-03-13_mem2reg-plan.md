# mem2reg — initial design plan

**Date:** 2026-03-13
**Branch:** mem2reg
**Files changed:** `ocaml_frontend/rewriters/core_mem2reg.ml`,
  `ocaml_frontend/rewriters/core_mem2reg.mli`,
  `ocaml_frontend/switches.ml`, `ocaml_frontend/switches.mli`,
  `backend/common/pipeline.ml`

## Goal

Implement a `mem2reg`-style optimisation pass that promotes function-local
variables whose address is never taken from stack-allocated Core objects
(Create / Store0 / Load0 / Kill sequences) to pure Core let-bindings.

The pass is gated on a new Cerberus switch `mem2reg`.  The transformed program
must be semantically equivalent to the original; it simply avoids unnecessary
memory operations for variables that never escape.

---

## Background: how C locals become Core

When the elaboration (`Translation.translate`) converts an AIL function body
containing `int x;` it:

1. Emits a `Create` memory action that allocates an object and binds a *pointer
   symbol* `ptr_x`:

   ```
   Esseq( Pattern([CaseBase(Some ptr_x, BTy_object OTy_pointer)]),
          Eaction(Paction(NA, Action(loc, (), Create(align_pe, ctype_pe,
                    PrefSource(ident_loc, [f_sym; x_sym]))))),
          body )
   ```

2. Every `x = v` assignment becomes a `Store0`:

   ```
   Esseq( Pattern([CaseBase(None, BTy_unit)]),
          Eaction(Paction(NA, Action(loc, (), Store0(false, ctype_pe,
                    PEsym ptr_x, val_pe, NA)))),
          continuation )
   ```

3. Every use of `x` becomes a `Load0`:

   ```
   Esseq( Pattern([CaseBase(Some loaded_x, BTy_loaded ...)]),
          Eaction(Paction(NA, Action(loc, (), Load0(ctype_pe,
                    PEsym ptr_x, NA)))),
          continuation )
   ```

4. At the end of the C scope, a `Kill` disposes of the allocation:

   ```
   Esseq( Pattern([CaseBase(None, BTy_unit)]),
          Eaction(Paction(NA, Action(loc, (), Kill(Static0 ctype, PEsym ptr_x)))),
          continuation )
   ```

The goal of mem2reg is to erase the Create/Kill and replace every Store0 with a
let-binding and every Load0 with a reference to the most recently stored value.

---

## Analysis level: AIL vs Core

The chosen approach is **Core-level analysis**.

### AIL-level analysis (rejected)

The AIL AST directly mirrors C surface syntax, so detecting address-of operations
is straightforward — pattern match on `AilEunary(Address, AilEident(sym))`.  Running
the analysis early gives access to richer variable context (storage class, declaration
location) and would let a simple set of promotable symbols be passed forward.

However three problems rule it out:

1. **Cross-level correlation.**  There is no explicit table mapping an AIL symbol for
   a local variable to its corresponding Core pointer symbol.  We would have to either
   (a) parse the `PrefSource` prefix in the Core transform, or (b) build the mapping
   during elaboration.  Both options are messy.

2. **Incomplete coverage — elaboration-generated address-taking.**  Some address-taking
   occurs *inside* the AIL→Core translation and does not appear as
   `AilEunary(Address, ...)` in the AIL AST at all.  Examples include compound
   literals, variadic argument passing, and certain builtins that take addresses
   internally during translation.  An AIL-level analysis would miss these and
   incorrectly conclude a variable is promotable when it is not.

3. **Pipeline coupling.**  Passing analysis results from the AIL phase to the Core
   phase requires threading state through the pipeline, touching the return type of
   `c_frontend_and_elaboration`, the signature of `core_passes`, and more.

4. **Qualifier handling.**  AIL analysis would need to explicitly check `register` and
   `volatile` qualifiers and skip them.  The Core analysis handles this implicitly: a
   `volatile` access compiles to an operation whose use pattern differs from a plain
   Load0/Store0, so it falls into `Use_other` and the variable is not promoted.

### Core-level analysis (chosen)

At the Core level, we inspect every use of a Create-bound pointer symbol.  If every
use is `Load0`, `Store0`, or `Kill`, it is promotable regardless of how the AIL
looked.

**Pros**

- **Self-contained.**  The entire pass lives in one file; no pipeline signature
  changes are needed.
- **Naturally handles implicit address-taking.**  Any elaboration artefact that
  passes `ptr_x` to a function or uses it in pointer arithmetic will produce a
  non-`Load0`/`Store0`/`Kill` use and the symbol will not be promoted — including
  the elaboration-generated cases that an AIL analysis would miss.
- **Covers Core-only inputs.**  When Cerberus is fed a `.core` file directly,
  the AIL program does not exist; the Core analysis still works.

**Cons**

- Requires understanding the structure of elaborated Core.  Mitigated by the
  conservative catch-all `Use_other` category.

---

## Phase 1 – Analysis: which pointer symbols are promotable?

Within each `Proc` body, a pointer symbol `ptr_x` (introduced by a `Create`)
is **promotable** if every occurrence of `PEsym ptr_x` is:

- The *address* argument of `Load0(_, PEsym ptr_x, _)`
- The *address* argument of `Store0(_, _, PEsym ptr_x, _, _)`
- The *pointer* argument of `Kill(_, PEsym ptr_x)`

And it does **not** appear in:

- Any function / procedure call argument list (`Eccall`, `Eproc`)
- `PEmember_shift(PEsym ptr_x, ...)` or `PEarray_shift(PEsym ptr_x, ...)`
- `PEmemop(_, pes)` where `PEsym ptr_x ∈ pes`
- Atomic operations: `SeqRMW`, `RMW0`, `CompareExchange{Strong,Weak}`,
  `LinuxLoad`, `LinuxStore`, `LinuxRMW`
- Any pure expression position not listed above
- A `CreateReadOnly` action
- Being stored through another pointer (`Store0(_, _, _, PEsym ptr_x, _)`)
- Anywhere under `Esave` (conservative: excludes loop-written vars)

**Implementation**: `collect_ptr_uses : Symbol.sym -> expr -> use list`

```ocaml
type use =
  | Use_load    (* Load0(_, PEsym ptr, _) – address arg *)
  | Use_store   (* Store0(_, _, PEsym ptr, _, _) – address arg *)
  | Use_kill    (* Kill(_, PEsym ptr) *)
  | Use_other   (* any other position *)
```

---

## Phase 2 – Transformation

```ocaml
type env = (Symbol.sym * Symbol.sym) list
(* maps ptr_sym -> current_val_sym (the last-stored value) *)

val transform_expr : env -> Symbol.SSet.t -> expr -> expr
```

### Straight-line cases

**Create** (promotable): drop it, recurse on body with same env.

**Store** (promotable):
```
Esseq(_, Store0(_, _, PEsym ptr_x, val_pe, _), cont)
→
Elet(CaseBase(new_val_sym, bty), Epure(val_pe),
     transform_expr (env[ptr_x ↦ new_val_sym]) promotable cont)
```
Fresh `new_val_sym` via `Cerb_fresh.fresh_sym ()`.

**Load** (promotable, ptr_x ∈ dom(env)):
```
Esseq(CaseBase(Some loaded_x, _), Load0(_, PEsym ptr_x, _), cont)
→
Elet(CaseBase(loaded_x, bty), Epure(PEsym (lookup env ptr_x)),
     transform_expr env promotable cont)
```
If `ptr_x ∉ dom(env)`: leave Load in place (UB path, safe to skip).

**Kill** (promotable): drop it, recurse on continuation.

### Branching: `Eif` and `Ecase`

For `Esseq(unit_pat, Eif(cond, e_true, e_false), cont)`:

1. Compute `written_vars = {ptr_x ∈ promotable | Store0(ptr_x) in e_true or e_false}`
2. If `written_vars = ∅`: transform branches and cont independently with same env.
3. If `written_vars ≠ ∅`:
   - Mint `phi_sym_x` for each `ptr_x ∈ written_vars`
   - Thread each branch to return final value of each `ptr_x` at its tail
   - `Eif` result becomes a tuple `(unit × loaded(ty_1) × ... × loaded(ty_n))`
   - Destructure tuple, bind `phi_sym_x` vars
   - Transform `cont` with `env` extended by `ptr_x ↦ phi_sym_x`

`Ecase` handled analogously (union of written_vars over all arms).

Branch-threading helper:
```ocaml
val thread_branch
  :  env
  -> Symbol.SSet.t
  -> Symbol.sym list   (* vars to thread *)
  -> expr              (* branch body *)
  -> Symbol.sym list   (* phi value syms produced *)
   * expr              (* transformed branch *)
```

### Loops (`Esave` / `Erun`)

Any `ptr_x` appearing under `Esave` is excluded from promotion (conservative).
This is enforced in the analysis phase.

### Non-matching expressions

Structural recursion: transform sub-expressions with current env.
(`Eccall`, `Eproc`, `Ewseq`, `Ebound`, `End`, `Epar`, `Ewait`)

---

## Files to create / modify

### 1. New: `ocaml_frontend/rewriters/core_mem2reg.ml`

Auto-compiled by `(include_subdirs unqualified)` in `ocaml_frontend/dune`.

Expose:
```ocaml
val transform_file : (unit, unit) Core.generic_file -> (unit, unit) Core.generic_file
```

### 2. Modified: `ocaml_frontend/switches.ml`

- Add `| SW_mem2reg` to `cerb_switch` type (after `SW_magic_comment_char_dollar`)
- Add `| "mem2reg" -> Some SW_mem2reg` in `read_switch`
- Add `| SW_mem2reg` to the simple-equality arm of `pred`

### 3. Modified: `ocaml_frontend/switches.mli`

Add `| SW_mem2reg` to `cerb_switch` type.

### 4. Modified: `backend/common/pipeline.ml`

In `core_passes`, after `Remove_unspecs.rewrite_file`, before `Core_indet.hackish_order`:

```ocaml
let core_file =
  if Switches.(has_switch SW_mem2reg) then
    Core_mem2reg.transform_file core_file
  else
    core_file in
```

---

## Concrete example

```c
int foo(int y) {
    int x = y + 1;
    return x;
}
```

Before:
```
Proc(foo, [y], integer,
  Esseq(ptr_x_pat, Create(...),
    Esseq(_, Store0(_, _, PEsym ptr_x, y+1, _),
      Esseq(loaded_x_pat, Load0(_, PEsym ptr_x, _),
        Esseq(_, Kill(_, PEsym ptr_x),
          Epure(PEsym loaded_x))))))
```

After:
```
Proc(foo, [y], integer,
  Elet(CaseBase(val_sym_0, ...),  Epure(y + 1),
    Elet(CaseBase(loaded_x, ...), Epure(PEsym val_sym_0),
      Epure(PEsym loaded_x))))
```

---

## Testing strategy

### Unit tests (`tests/ci/`)

| File | What it tests |
|---|---|
| `mem2reg_simple.c` | Single local, straight-line init + return |
| `mem2reg_multi.c` | Multiple independent locals in one function |
| `mem2reg_if.c` | Local written in both branches of an `if`, read after |
| `mem2reg_if_one_branch.c` | Local written in only one branch, read after |
| `mem2reg_loop.c` | Local written before a `while` loop, not inside it |
| `mem2reg_no_promote_address.c` | `&x` taken — must NOT be promoted |
| `mem2reg_no_promote_arg.c` | Local passed to a function — must NOT be promoted |
| `mem2reg_no_promote_loop_write.c` | Local written inside a loop body — not promoted |
| `mem2reg_struct.c` | Struct local — not promoted (member-shift disqualifies it) |
| `mem2reg_mixed.c` | Function with both promotable and non-promotable locals |

### Regression

```sh
for file in ci/*.c; do
  cerberus --exec --batch "$file" > tmp/base.out 2>&1
  cerberus --exec --batch --sw mem2reg "$file" > tmp/opt.out 2>&1
  diff -q tmp/base.out tmp/opt.out || echo "REGRESSION: $file"
done
```

### Core inspection

```sh
cerberus --pp core --sw mem2reg mem2reg_simple.c          # Create/Kill must be gone
cerberus --pp core --sw mem2reg mem2reg_no_promote_address.c  # Create/Kill must remain
```

### Typechecking

```sh
cerberus --typecheck-core --sw mem2reg tests/ci/mem2reg_*.c
```

### Negative promotion (grep-based)

```sh
cerberus --pp core --sw mem2reg mem2reg_no_promote_address.c | grep -q "create" \
  && echo "PASS" || echo "FAIL: variable incorrectly promoted"
```

---

## Out-of-scope / future work

- Promoting struct/union locals (member-shift uses disqualify them)
- Loop-carried promotions (variables written inside a loop body)
- CN interaction (pass should run before CN annotations are processed)
