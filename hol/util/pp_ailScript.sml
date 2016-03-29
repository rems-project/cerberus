open HolKernel Parse boolLib bossLib finite_mapTheory;

open ailTypesTheory ailSyntaxTheory;

val _ = new_theory "pp_ail"

val _ = Define `
  pp_ail_ctype (c :ailTypes$ctype) = ""`;

val _ = Define `
  pp_qualifiers (a: ailTypes$qualifiers) = ""`;

(**
* Suporting definitions for decode.lem
**)

val _ = Define `
  decode_num (s:string) = (ailSyntax$Decimal, 0 : int)`;

val _ = Define `
  decode_char (s:string) = 0:int`;

val _ = Define `
  encode_char (n:int) = ""`;

val _ = export_theory()
