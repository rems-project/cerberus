type ('spec, 'res) t = {
    spec : 'spec;
    resolved : 'res option
  }


let find_resolved env unis = 
  SymMap.foldM
    (fun usym ({spec; resolved} as uni) (unresolved,substs) ->
      match resolved with
      | None ->
         Except.return (SymMap.add usym uni unresolved, substs)
      | Some sym -> 
         let (LogicalSorts.Base bt) = spec in
         (* check_it loc_call (S (sym, bt)) bt >> *)
         Except.return (unresolved, (usym, sym) :: substs)
    ) unis (SymMap.empty, [])

