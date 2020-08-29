open Subst
module SymSet = Set.Make(Sym)

type 'res t = { resolved : 'res option }

let find_resolved env unis = 
  SymMap.fold
    (fun usym {resolved} (unresolveds,resolveds) ->
      match resolved with
      | None -> (usym :: unresolveds, resolveds)
      | Some sym -> (unresolveds, ({s=usym; swith=sym}) :: resolveds)
    ) unis ([], [])


let unresolved_var unis (vars : SymSet.t) =
  SymMap.fold
    (fun usym {resolved} found ->
      match resolved with
      | None when SymSet.mem usym vars -> Some usym
      | _ -> found
    ) unis None


