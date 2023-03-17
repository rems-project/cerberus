open Cerb_frontend

type 'a cn_injection = {
  filename: string;
  sigm: 'a AilSyntax.sigma;
  pre_post: (Symbol.sym * (string * string)) list;
  in_stmt: (Location_ocaml.t * string) list;
}

val output_injections: Stdlib.out_channel -> 'a cn_injection -> (unit, string) Result.result