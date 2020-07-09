module CF = Cerb_frontend
module S = CF.Symbol

type symbol = S.sym
type t = symbol


let fresh = S.fresh
let fresh_pretty = S.fresh_pretty


let pp_string = CF.Pp_symbol.to_string_pretty ~compact:true
let pp sym = Pp.string (pp_string sym)



let compare = S.symbol_compare


