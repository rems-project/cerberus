open HolKernel Parse boolLib bossLib finite_mapTheory;

open ailTypesTheory core_ctypeTheory defacto_memory_typesTheory;

val _ = new_theory "util"

val _ = Define `
  print_debug (n:num) (s:string) = ()`;

val _ = Define `
  print_debug2 (s:string) (u:'a) = u`;

val _ = Define `
  emptyString (x:'a) = ""`;

val _ = Define `
  pickList (l : 'a list) = ARB : ('a list # 'a # 'a list)`;

val _ = Define `
  unitId (u:unit) = ()`;

val _ = Define `
  print_debug_located (n:num) (l:unit) (s:string) = ()`;

val _ = Hol_datatype `
 execution_mode =
    Interactive
  | Exhaustive
  | Random`;

val _ = Define `
  current_execution_mode (u:unit) = SOME Random`;

val _ = Define `
  user_request_driver (l: string list) = (0:num)`;

val _ = Define `
  output_string (s:string) = ()`;

val _ = Define `
  nat_of_string (s :string) = (0:int)`;

val _ = export_theory()
