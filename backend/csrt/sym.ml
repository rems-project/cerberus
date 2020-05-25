open Tools
open Subst
module CF = Cerb_frontend
module S = CF.Symbol
open Option

type symbol = S.sym
type t = symbol


let fresh = S.fresh
let fresh_pretty = S.fresh_pretty
let pp sym = PPrint.string (CF.Pp_symbol.to_string_pretty sym)

let compare = S.symbol_compare







module Uni = struct

type ('spec, 'res) t = {
    spec : 'spec;
    resolved : 'res option
  }


let find_resolved env unis = 
  SymMap.foldM
    (fun usym {spec; resolved} (unresolveds,resolveds) ->
      match resolved with
      | None ->
         Except.return (SymMap.add usym spec unresolveds, resolveds)
      | Some sym -> 
         Except.return (unresolveds, (spec, {substitute=usym; swith=sym}) :: resolveds)
    ) unis (SymMap.empty, [])

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
       let uni = { uni with resolved = Some sym' } in
       return (SymMap.add sym uni res)
