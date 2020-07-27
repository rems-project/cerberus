module CF = Cerb_frontend
module CB = Cerb_backend
module Loc = Locations

module StringMap = Map.Make(String)


let concat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)


let id = fun x -> x

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)



let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false




let symmap_lookup (loc : Loc.t) (e: 'v SymMap.t) (name: Sym.t) =
  let open Except in
  match SymMap.find_opt name e with
  | None -> fail loc (TypeErrors.Unbound_name name)
  | Some v -> return v


let symmap_foldM 
      (f : Sym.t -> 'a -> 'b -> 'b Except.m)
      (m : 'a SymMap.t)
      (acc : 'b)
    : 'b Except.m =
  let open Except in
  SymMap.fold (fun sym a m_acc ->
      let* acc = m_acc in
      f sym a acc
    ) m (return acc)

let symmap_iterM 
      (f : Sym.t -> 'a -> 'b -> (unit,'e) Except.t)
      (m : 'a SymMap.t)
    : unit Except.m =
  symmap_foldM f m ()

let symmap_filter
      (f : Sym.t -> 'a -> bool Except.m)
      (m : 'a SymMap.t)
    : ('a SymMap.t) Except.m =
  let open Except in
  symmap_foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (if c then SymMap.add sym a acc else acc)
    )
    m SymMap.empty

let symmap_filter_map_list
      (f : Sym.t -> 'a -> ('b option) Except.m)
      (m : 'a SymMap.t)
    : ('b list) Except.m =
  let open Except in
  symmap_foldM 
    (fun sym a acc ->
      let* c = f sym a in
      match c with
      | Some r -> return (acc@[r])
      | None -> return acc
    )
    m []


let symmap_for_all
      (f : Sym.t -> 'a -> bool Except.m)
      (m : 'a SymMap.t)
    : bool Except.m =
  let open Except in
  symmap_foldM 
    (fun sym a acc ->
      let* c = f sym a in
      return (acc && c)
    )
    m true



let precise_loc loc mlock = 
  match mlock with
  | Some loc2 -> loc2
  | None -> loc


let update_loc loc annots =
  precise_loc loc (CF.Annot.get_loc annots)
  
let aunpack loc (CF.Mucore.Annotated (annots, _, x)) = 
  (x, update_loc loc annots)





open Except

let at_most_one loc err_str = function
  | [] -> return None
  | [x] -> return (Some x)
  | _ -> fail loc (TypeErrors.Generic_error err_str)

let assoc_err loc entry list err =
  match List.assoc_opt entry list with
  | Some result -> return result
  | None -> fail loc err

(* let rassoc_err loc entry list err =
 *   let rec aux = function
 *     | [] -> None
 *     | (a,entry') :: rest -> 
 *        if entry = entry' then Some a else aux rest
 *   in
 *   match aux list with
 *   | Some result -> return result
 *   | None -> fail loc err *)
