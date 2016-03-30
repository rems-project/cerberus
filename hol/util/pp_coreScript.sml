open HolKernel Parse boolLib bossLib finite_mapTheory;

open core_ctypeTheory coreTheory memTheory symbolTheory;

val _ = new_theory "pp_core"

(**
* Suporting definitions for boot.lem
**)

val _ = Define `
  pp_core_ctype (c :ctype) = ""`;

val _ = Define `
  pp_core_expr (e :'a expr) = ""`

val _ = Define `
  pp_core_pexpr (e : pexpr) = ""`;

val _ = Define `
  pp_core_value (v :value) = ""`;

val _ = Define `
  pp_prefix (s :symbol$prefix) = ""`;

val _ = Define `
  pp_core_file (f :'a core$file) = ""`;

val _ = Define `
  pp_core_stack (f :'a core$stack) = ""`;

val _ = Define `
  pp_core_params (p :(symbol$t1 # core$core_base_type) list) = ""`;


val _ = export_theory()
