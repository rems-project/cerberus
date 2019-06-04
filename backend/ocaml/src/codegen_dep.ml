(* Created by Victor Gomes 2017-05-06 *)

open Util
open Pp_prelude
open Pp_ocaml

let print_section sectname =
  List.fold_left (fun acc s -> acc ^/^ print_global_symbol s) !^sectname

let gen fl externs funs globs =
  let contents =
    print_section ".unresolved" externs ^/^
    print_section ".funs" (Pset.elements $ Pmap.domain funs) ^/^
    print_section ".data" globs
  in
  let fl_dep = fl ^ ".sym" in
  let oc = open_out fl_dep in
  P.ToChannel.pretty 1. 80 oc contents;
  close_out oc
