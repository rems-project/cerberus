module Loc = Locations

let lookup (loc : Loc.t) (e: 'v SymMap.t) (name: Sym.t) =
  let open Except in
  match SymMap.find_opt name e with
  | None -> fail loc (TypeErrors.Unbound_name name)
  | Some v -> return v


let foldM 
      (f : Sym.t -> 'a -> 'b -> ('b,'e) Except.t)
      (m : 'a SymMap.t)
      (acc : 'b)
    : ('b,'e) Except.t =
  let open Except in
  SymMap.fold (fun sym a m_acc ->
      let* acc = m_acc in
      f sym a acc
    ) m (return acc)

let iterM 
      (f : Sym.t -> 'a -> 'b -> (unit,'e) Except.t)
      (m : 'a SymMap.t)
    : (unit,'e) Except.t =
  foldM f m ()

let filter
      (f : Sym.t -> 'a -> (bool,'e) Except.t)
      (m : 'a SymMap.t)
    : ('a SymMap.t,'e) Except.t =
  let open Except in
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (if c then SymMap.add sym a acc else acc)
    )
    m SymMap.empty

let filter_map_list
      (f : Sym.t -> 'a -> ('b option,'e) Except.t)
      (m : 'a SymMap.t)
    : ('b list,'e) Except.t =
  let open Except in
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      match c with
      | Some r -> return (acc@[r])
      | None -> return acc
    )
    m []


let for_all
      (f : Sym.t -> 'a -> (bool,'e) Except.t)
      (m : 'a SymMap.t)
    : (bool,'e) Except.t =
  let open Except in
  foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (acc && c)
    )
    m true  
