module CF = Cerb_frontend
module S = CF.Symbol

include S


type t = S.sym

let fresh = S.fresh
let fresh_named = S.fresh_pretty
let fresh_onamed = S.fresh_fancy

let fresh_relative (s : t) (f : string -> string) : t =
  match symbol_name s with
  | Some name -> fresh_named (f name)
  | None -> fresh ()

let fresh_same s = fresh_relative s (fun id -> id)


let pp_string = CF.Pp_symbol.to_string_pretty ~compact:true
let pp sym = Pp.string (pp_string sym)


let equal = S.symbolEquality
let compare = S.symbol_compare


let named (s : t) : bool =
  Option.is_some (symbol_name s)


open Subst

let subst {before;after} symbol = 
  if symbol = before then after else symbol



