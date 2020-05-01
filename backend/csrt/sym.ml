open Cerb_frontend

type symbol = Symbol.sym
type t = symbol


let fresh = Symbol.fresh
let fresh_pretty = Symbol.fresh_pretty
let pp sym = PPrint.string (Pp_symbol.to_string_pretty sym)

let compare = Symbol.symbol_compare

let subst replace with_sym symbol = 
  if symbol = replace then with_sym else symbol



