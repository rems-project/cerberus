module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms

let ocaml_int_bt = BT.Bits (Signed, Sys.int_size + 1)

let names = ref []

let get_mangled_name (syms : Sym.t list) : Sym.t =
  let open Pp in
  if GenBuiltins.is_builtin (List.hd syms) then
    List.hd syms
  else (
    match List.assoc_opt (List.equal Sym.equal) syms !names with
    | Some sym -> sym
    | None ->
      let doc = string "cn_gen_" ^^ separate_map underscore Sym.pp syms in
      let res_sym = Sym.fresh_named (CF.Pp_utils.to_plain_string doc) in
      names := (syms, res_sym) :: !names;
      res_sym)
