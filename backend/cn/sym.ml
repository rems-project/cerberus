module CF = Cerb_frontend
module S = CF.Symbol
open Pp

include S


type t = S.sym
type sym = t

let equal = S.symbolEquality
let compare = S.symbol_compare


type description = S.symbol_description


let description (s : t) : description = S.symbol_description s


let dest = function
  | CF.Symbol.Symbol (digest, nat, oname) ->
     (digest, nat, oname)

let pp_string = CF.Pp_symbol.to_string_pretty
let pp sym = Pp.string (pp_string sym)
let pp_debug sym = Pp.string (CF.Symbol.show_raw_less sym)

let num = S.symbol_num

let fresh () = S.fresh ()

let fresh_named = S.fresh_pretty
let fresh_description = S.fresh_description

let fresh_same (s : t) : t =
  fresh_description (S.symbol_description s)


open Subst

let subst (subst: (sym, sym) Subst.t) symbol = 
  if equal symbol subst.before then subst.after else symbol



let substs = make_substs subst


let json sym = `String (pp_string sym)
