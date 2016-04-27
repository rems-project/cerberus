open HolKernel Parse boolLib bossLib finite_mapTheory;

open core_ctypeTheory coreTheory memTheory;

val _ = new_theory "pp_mem"

(**
* Suporting definitions for output.lem
**)

val _ = Define `
  pp_mem_value (m:mem_value0) = ""`;

val _ = Define `
  pp_pointer_value (p:pointer_value0) = ""`;

val _ = export_theory()
