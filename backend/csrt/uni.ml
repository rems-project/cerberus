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
         Except.return (unresolveds, (spec, (usym, sym)) :: resolveds)
    ) unis (SymMap.empty, [])
    
