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


open Option

let unify_sym sym sym' (res : (Sym.t t) SymMap.t) = 
  if sym = sym' then Some res else
    let* uni = SymMap.find_opt sym res in
    begin match uni.resolved with
    | Some s when s = sym' -> return res 
    | Some s -> fail
    | None -> return (SymMap.add sym {resolved = Some sym'} res)
    end

