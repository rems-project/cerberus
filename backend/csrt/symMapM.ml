open Resultat
module Loc = Locations
module SymMap = Map.Make(Sym)

let lookup (loc : Loc.t) (e: 'v SymMap.t) (name: Sym.t) =
  match SymMap.find_opt name e with
  | None -> fail loc (TypeErrors.Unbound_name (Sym name))
  | Some v -> return v


let foldM 
      (f : Sym.t -> 'a -> 'b -> ('b,'e) result)
      (m : 'a SymMap.t)
      (acc : 'b)
    : ('b,'e) result =
  SymMap.fold (fun sym a m_acc ->
      let* acc = m_acc in
      f sym a acc
    ) m (return acc)

let iterM 
      (f : Sym.t -> 'a -> 'b -> (unit,'e) result)
      (m : 'a SymMap.t)
    : (unit,'e) result =
  foldM f m ()

let filter
      (f : Sym.t -> 'a -> (bool,'e) result)
      (m : 'a SymMap.t)
    : ('a SymMap.t,'e) result =
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (if c then SymMap.add sym a acc else acc)
    )
    m SymMap.empty

let filter_map_list
      (f : Sym.t -> 'a -> ('b option,'e) result)
      (m : 'a SymMap.t)
    : ('b list,'e) result =
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      match c with
      | Some r -> return (acc@[r])
      | None -> return acc
    )
    m []


let for_all
      (f : Sym.t -> 'a -> (bool,'e) result)
      (m : 'a SymMap.t)
    : (bool,'e) result =
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (acc && c)
    )
    m true  
