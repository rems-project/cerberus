open Cerb_frontend

type 'a cn_injection = {
  filename: string;
  sigm: 'a AilSyntax.sigma;
  pre_post: (Symbol.sym * (string list * string list)) list;
  in_stmt: (Cerb_location.t * string list) list;
}

val output_injections: Stdlib.out_channel -> 'a cn_injection -> (unit, string) Result.result
val get_magics_of_statement: 'a AilSyntax.statement -> (Cerb_location.t * string) list list