open HolKernel Parse boolLib bossLib finite_mapTheory;

val _ = new_theory "pp"

val _ = Hol_datatype `
 execution_mode =
    Interactive
  | Exhaustive
  | Random`;

val _ = Define `
  current_execution_mode (u:unit) = Some Random`;

val _ = Define `
  user_request_driver (l: string list) = (0:num)`;

val _ = export_theory()
