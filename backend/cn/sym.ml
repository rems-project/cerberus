module CF = Cerb_frontend
module S = CF.Symbol

(* include S *)


type t = S.sym
type sym = t

let equal = S.symbolEquality
let compare = S.symbol_compare

let name (s : t) : string option = S.symbol_name s
let named (s : t) : bool = Option.is_some (S.symbol_name s)


let pp_string = CF.Pp_symbol.to_string_pretty
let pp sym = Pp.string (pp_string sym)
let pp_debug sym = Pp.string (CF.Symbol.show_raw_less sym)

let num = S.symbol_num

let fresh = S.fresh
let fresh_named = S.fresh_pretty


let fresh_same (s : t) : t =
  match S.symbol_name s with
  | Some name -> fresh_named name
  | None -> fresh ()


open Subst

let subst (subst: (sym, sym) Subst.t) symbol = 
  if equal symbol subst.before then subst.after else symbol



let substs = make_substs subst


let json sym = `String (pp_string sym)
