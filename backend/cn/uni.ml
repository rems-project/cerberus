open Subst
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

type 'res uni = { resolved : 'res option }

type 'res unis = ('res uni) SymMap.t

type 'res t = 'res unis

let find_resolved env unis = 
  SymMap.fold (fun usym {resolved} resolveds ->
      match resolved with
      | None -> resolveds
      | Some sym -> ({before=usym; after=sym}) :: resolveds
    ) unis []


