open Cerb_frontend
open Option
open Uni

type symbol = Symbol.sym
type t = symbol


let fresh = Symbol.fresh
let fresh_pretty = Symbol.fresh_pretty
let pp sym = PPrint.string (Pp_symbol.to_string_pretty sym)

let compare = Symbol.symbol_compare

let subst replace with_sym symbol = 
  if symbol = replace then with_sym else symbol


let unify sym sym' res = 
  if sym = sym' then Some res
  else
   SymMap.find_opt sym res >>= fun uni ->
   match uni.resolved with
   | Some s when s = sym' -> return res 
   | Some s -> fail
   | None -> 
      let uni = { uni with resolved = Some sym' } in
      return (SymMap.add sym uni res)
