include Result
module Loc = Locations


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

let (let@) = bind




let unsupported (loc : Loc.t) (err : Pp.document) : 'a = 
  let trace = Option.map Pp.string (Tools.do_stack_trace ()) in
  Pp.error loc err (Option.to_list trace);
  exit 2



type ('a,'e) m = ('a, 'e error) Result.t


let msum (m1 : ('a,'e) t) (m2 : (('a,'e) t) Lazy.t) : ('a,'e) t = 
  match m1 with
  | Ok a -> Ok a
  | Error _ -> Lazy.force m2


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
         let@ y = f x in
         let@ ys = aux xs in
         return (y :: ys)
    in
    aux l


  let mapiM (f : int -> 'a -> ('b,'e) result) 
            (l : 'a list) : ('b list, 'e) result = 
    let rec aux i l =
      match l with
      | [] -> return []
      | x :: xs -> 
         let@ y = f i x in
         let@ ys = aux (i + 1) xs in
         return (y :: ys)
    in
    aux 0 l

  let iterM (f : ('a -> (unit,'e) result)) (l : 'a list) : (unit, 'e) result = 
    let@ _ = mapM f l in 
    return ()

  let concat_mapM f l = 
    let@ xs = mapM f l in
    return (concat xs)

  let filter_mapM f l = 
    let@ xs = mapM f l in
    return (filter_map (fun x -> x) xs)



  let fold_leftM (f : 'a -> 'b -> ('c,'e) result) (a : 'a) (bs : 'b list) =
    Stdlib.List.fold_left (fun aM b -> let@ a = aM in f a b) (return a) bs

  (* maybe from Exception.lem *)
  let fold_rightM (f : 'b -> 'a -> ('c,'e) result) (bs : 'b list) (a : 'a) =
    Stdlib.List.fold_right (fun b aM -> let@ a = aM in f b a) bs (return a)

end

module List1M = struct

  open List1

  let mapM (f : 'a -> ('b,'e) result) (l : 'a list1) : ('b list1, 'e) result = 
    let (hd, tl) = dest l in
    let@ hd = f hd in
    let@ tl = ListM.mapM f tl in
    return (List1.make (hd, tl))

  let iterM (f : ('a -> (unit,'e) result)) (l : 'a list1) : (unit, 'e) result = 
    let@ _ = mapM f l in 
    return ()  

end


module PmapM = struct

  let foldM 
        (f : 'k -> 'x -> 'y -> ('y,'e) t)
        (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) t =
    Pmap.fold (fun k v aM -> let@ a = aM in f k v a) map (return init)

  let iterM f m = 
    Pmap.fold (fun k v m -> let@ () = m in f k v) 
      m (return ())

  let mapM 
        (f: 'k -> 'v -> ('w,'e) t)
        (m : ('k,'v) Pmap.map)
        (cmp: 'k -> 'k -> int)
      : (('k,'w) Pmap.map, 'e) t
    = 
    foldM (fun k v m -> 
        let@ v' = f k v in 
        return (Pmap.add k v' m)
      ) m (Pmap.empty cmp)

end


