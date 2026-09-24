# Plan: `save_to_where` Core pass — Phase 1: scaffold

## Context

`Ewhere`/`Ejump` constructors are now fully wired into the Core IR, typing,
and all passes. The next step is a new rewriter `save_to_where` that will
transform procedures using `Esave`/`Erun` into ones using `Ewhere`/`Ejump`.
Phase 1 is purely structural: add the switch, create a no-op pass, and wire
it into the pipeline so the scaffold builds and runs cleanly before any
transformation logic is added.

---

## Files to modify


### 0. Save plan

Save this plan with an appropriate name to the `doc/` directory.

### 1. `ocaml_frontend/switches.mli`

Add after `SW_copy_prop`:
```ocaml
| SW_save_to_where
```

### 2. `ocaml_frontend/switches.ml`

Three locations, mirroring `SW_copy_prop`:

**Constructor** (after `SW_copy_prop`):
```ocaml
| SW_save_to_where
```

**`read_switch`** (after the `"copy_prop"` case, before `| _ -> None`):
```ocaml
| "save_to_where" -> Some SW_save_to_where
```

**Simple-equality arm of `pred`** (add to the list ending with `SW_copy_prop`):
```ocaml
| SW_save_to_where as y ->
```

### 3. `ocaml_frontend/rewriters/save_to_where.ml` — new file

No-op pass, pattern identical to `remove_unspecs.ml` / `copy_propagation.ml`:
```ocaml
let transform_file core_file = core_file
```

### 4. `backend/common/pipeline.ml`

After the `copy_prop` block (line ~574), add:
```ocaml
let core_file =
  if Switches.(has_switch SW_save_to_where) then
    Save_to_where.transform_file core_file
  else
    core_file in
```

---

## Verification

```sh
make && make install
cerberus --exec --batch tests/ci/0001.c          # baseline still works
cerberus --sw save_to_where --exec --batch tests/ci/0001.c  # no-op, same output
```
