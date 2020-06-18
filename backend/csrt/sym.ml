open Subst
module CF = Cerb_frontend
module S = CF.Symbol
open Option

type symbol = S.sym
type t = symbol


let fresh = S.fresh
let fresh_pretty = S.fresh_pretty


let pp_string = CF.Pp_symbol.alt_to_string_pretty
let pp sym = Pp.string (pp_string sym)



let compare = S.symbol_compare







module Uni = struct

type 'res t = { resolved : 'res option }

let find_resolved env unis = 
  SymMap.fold
    (fun usym {resolved} (unresolveds,resolveds) ->
      match resolved with
      | None -> (usym :: unresolveds, resolveds)
      | Some sym -> (unresolveds, ({substitute=usym; swith=sym}) :: resolveds)
    ) unis ([], [])

end
    

open Uni



let subst (subst : (symbol,symbol) Subst.t) (symbol : symbol) : symbol = 
  if symbol = subst.substitute then subst.swith else symbol

let substs = make_substs subst



let unify sym sym' res = 
  if sym = sym' then Some res
  else
    let* uni = SymMap.find_opt sym res in
    match uni.resolved with
    | Some s when s = sym' -> return res 
    | Some s -> fail
    | None -> 
       let uni = { resolved = Some sym' } in
       return (SymMap.add sym uni res)
