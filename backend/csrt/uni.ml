open Subst

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
    

