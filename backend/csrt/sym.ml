open Cerb_frontend

type symbol = Symbol.sym
type t = symbol


let fresh = Symbol.fresh
let fresh_pretty = Symbol.fresh_pretty
let pp = Pp_symbol.to_string_pretty

let compare = Symbol.symbol_compare

let sym_subst replace with_sym symbol = 
  if symbol = replace then with_sym else symbol



