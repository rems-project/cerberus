include Result



let return (a: 'a) : ('a,'e) t = 
  Ok a

let error (e: 'e) : ('a,'e) t = 
  Error e

type 'e error = Locations.loc * Tools.stacktrace option * 'e

let fail (loc: Locations.loc) (e: 'e) : ('a, 'e error) t = 
  error (loc, Tools.do_stack_trace (),  e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind



type ('a,'e) m = ('a, 'e error) Result.t


let lift_error (f : 'e1 -> 'e2) (m : ('a,'e1) m) : ('a,'e2) m =
  match m with
  | Ok a -> Ok a
  | Error (loc, stacktrace, e1) -> 
     Error (loc, stacktrace, f e1)


let msum (m1 : ('a,'e) t) (m2 : ('a,'e) t) : ('a,'e) t = 
  match m1 with
  | Ok a -> Ok a
  | Error _ -> m2







let assoc_err loc equality entry list err =
  match List.assoc_opt equality entry list with
  | Some result -> return result
  | None -> fail loc err




module ListM = struct

  open List

  let mapM (f : 'a -> ('b,'e) result) (l : 'a list) : ('b list, 'e) result = 
    let rec aux = function
      | [] -> return []
      | x :: xs -> 
         let* y = f x in
         let* ys = aux xs in
         return (y :: ys)
    in
    aux l


  let mapiM (f : int -> 'a -> ('b,'e) result) 
            (l : 'a list) : ('b list, 'e) result = 
    let rec aux i l =
      match l with
      | [] -> return []
      | x :: xs -> 
         let* y = f i x in
         let* ys = aux (i + 1) xs in
         return (y :: ys)
    in
    aux 0 l

  let iterM (f : ('a -> (unit,'e) result)) (l : 'a list) : (unit, 'e) result = 
    let* _ = mapM f l in 
    return ()

  let concat_mapM f l = 
    let* xs = mapM f l in
    return (concat xs)

  let filter_mapM f l = 
    let* xs = mapM f l in
    return (filter_map (fun x -> x) xs)



  let fold_leftM (f : 'a -> 'b -> ('c,'e) result) (a : 'a) (bs : 'b list) =
    Stdlib.List.fold_left (fun aM b -> let* a = aM in f a b) (return a) bs

  (* maybe from Exception.lem *)
  let fold_rightM (f : 'b -> 'a -> ('c,'e) result) (bs : 'b list) (a : 'a) =
    Stdlib.List.fold_right (fun b aM -> let* a = aM in f b a) bs (return a)

end


module SymMapM = struct

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

end




module PmapM = struct

  let foldM 
        (f : 'k -> 'x -> 'y -> ('y,'e) t)
        (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) t =
    Pmap.fold (fun k v aM -> let* a = aM in f k v a) map (return init)

  let iterM f m = 
    Pmap.fold (fun k v m -> let* () = m in f k v) 
      m (return ())

  let mapM 
        (f: 'k -> 'v -> ('w,'e) t)
        (m : ('k,'v) Pmap.map)
        (cmp: 'k -> 'k -> int)
      : (('k,'w) Pmap.map, 'e) t
    = 
    foldM (fun k v m -> 
        let* v' = f k v in 
        return (Pmap.add k v' m)
      ) m (Pmap.empty cmp)

end
