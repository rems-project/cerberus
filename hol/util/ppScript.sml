open HolKernel Parse boolLib bossLib finite_mapTheory;

open ailTypesTheory ailSyntaxTheory core_ctypeTheory coreTheory memTheory
core_runTheory cmm_opTheory symbolicTheory;

val _ = new_theory "pp"

val _ = Define `
  print_debug (n:nat) (s:string) = ()`;

val _ = Define `
  print_debug2 (s:string) (u:'a) = u`;


(**
* Suporting definitions for boot.lem
**)

val _ = Define `
  empryString (x:'a) = ""`;

val _ = Define `
  pickList (l : 'a list) = ARB : ('a list # 'a # 'a list)`;


val _ = Define `
  unitId (u:unit) = ()`;

val _ = Define `
  output_string (s:string) = ()`;

val _ = Define `
  print_debug_located (n:nat) (l:unit) (s:string) = ()`;

val _ = Define `
  pp_ail_ctype (c :ailTypes$ctype) = ""`;

val _ = Define `
  pp_core_ctype (c :ctype0) = ""`;

val _ = Define `
  pp_core_expr (e :'a core$expr) = ""`;

val _ = Define `
  pp_core_pexpr (e core$pexpr) = ""`;

val _ = Define `
  pp_core_value (v :core$value) = ""`;

val _ = Define `
  pp_prefix (s :symbol$prefix) = ""`;

val _ = Define `
  nat_of_string (s :string) = (0:int)`;

val _ = Define `
  pp_core_file (f :'a core$file) = ""`;

val _ = Define `
  pp_core_params (p :(symbol$t2 # core$core_base_type) list) = ""`;

(**
* Suporting definitions for decode.lem
**)

val _ = Define `
  decode_num (s:string) = (ailSyntax$Decimal, 0 : num)`;

val _ = Define `
  decode_char (s:string) = 0:num`;

val _ = Define `
  encode_char (n:num) = ""`;

(**
* Suporting definitions for output.lem
**)

val _ = Define `
  stringFromMemValue (m:mem_value0) = ""`;

val _ = Define `
  stringFromPointerValue (p:pointer_value0) = ""`;

(**
* Suporting definitions for cabs_to_ail.lem
**)


val _ = Define `
  stringFromQualifiers (a: ailTypes$qualifiers) = ""`;

(**
* Suporting definitions for driver.lem
**)

val _ = Define `
  pp_core_state (a: core_state) = ""`;

val _ = Define `
  pp_sym_state (a: symState) = ""`;

val _ = Define `
  pp_symbolic (a: symbolic) (ov: object_value) (pv: pointer_value) = ""`;




val _ = export_theory()
