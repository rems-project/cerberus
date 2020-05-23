open Tools
open Subst
open Cerb_frontend
open Option

type symbol = Symbol.sym
type t = symbol


let fresh = Symbol.fresh
let fresh_pretty = Symbol.fresh_pretty
let pp sym = PPrint.string (Pp_symbol.to_string_pretty sym)

let compare = Symbol.symbol_compare







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
   SymMap.find_opt sym res >>= fun uni ->
   match uni.resolved with
   | Some s when s = sym' -> return res 
   | Some s -> fail
   | None -> 
      let uni = { uni with resolved = Some sym' } in
      return (SymMap.add sym uni res)
