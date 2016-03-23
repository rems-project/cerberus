open HolKernel Parse boolLib bossLib finite_mapTheory;

open core_ctypeTheory defacto_memory_typesTheory;

val _ = new_theory "util"

(**
 * Suporting defintion for core_ctype_aux
 * Equivalent to src/tags
 **)

val _ = Define `
  tagDefs (u:unit) = FEMPTY : (member_id |-> (cabs_identifier # ctype0) list)`;

val _ = Define `
  set_tagDefs (u : (member_id |-> (cabs_identifier # ctype0) list)) = ()`;

(**
 * Suporting defintion for defacto_memory
 **)

val _ = Define `
  easy_update_mem_value_aux (b:bool) (c:ctype0) (sp:shift_path) (mv:mem_value) (mv':mem_value) = mv`;

val _ = export_theory()
