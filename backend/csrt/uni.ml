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


let unresolved_var unis (vars : SymSet.t) =
  SymMap.fold (fun usym {resolved} found ->
      match resolved with
      | None when SymSet.mem usym vars -> Some usym
      | _ -> found
    ) unis None


open Option

let unify_sym sym sym' (res : Sym.t t) = 
  if sym = sym' then Some res else
    let* uni = SymMap.find_opt sym res in
    begin match uni.resolved with
    | Some s when s = sym' -> return res 
    | Some s -> fail
    | None -> return (SymMap.add sym {resolved = Some sym'} res)
    end

