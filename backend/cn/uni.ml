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


let unresolved_var (unis : 'res unis) (vars : SymSet.t) =
  SymSet.fold (fun var found ->
      match SymMap.find_opt var unis with
      | None -> found
      | Some {resolved = Some _} -> found
      | Some {resolved = None} -> Some var
    ) vars None

let all_resolved unis vars = 
  Option.is_none (unresolved_var unis vars)






