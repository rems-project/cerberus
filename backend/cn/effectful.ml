module type S = sig
  type ('a, 'e) m
  val return : 'a -> ('a, 'e) m
  val bind : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
end



module Make(T : S) = struct

  open T

  let (let@) = T.bind


  module ListM = struct

    open List

    let rec mapM (f : 'a -> ('b, 'e) m) (l : 'a list) : ('b list, 'e) m = 
      match l with
      | [] -> return []
      | x :: xs -> 
         let@ y = f x in
         let@ ys = mapM f xs in
         return (y :: ys)

    let mapfstM (f : 'a -> ('c, 'e) m) (l : ('a * 'b) list) : (('c * 'b) list, 'e) m =
      mapM (fun (a, b) -> let@ c = f a in return (c, b)) l

    let mapsndM (f : 'b -> ('c, 'e) m) (l : ('a * 'b) list) : (('a * 'c) list, 'e) m = 
      mapM (fun (a, b) -> let@ c = f b in return (a, c)) l



    let mapiM (f : int -> 'a -> ('b, 'e) m) 
              (l : 'a list) : ('b list, 'e) m = 
      let rec aux i l =
        match l with
        | [] -> return []
        | x :: xs -> 
           let@ y = f i x in
           let@ ys = aux (i + 1) xs in
           return (y :: ys)
      in
      aux 0 l

    let map2M (f : 'a -> 'b -> ('c, 'e) m)
              (l1 : 'a list)
              (l2 : 'b list)
            : ('c list, 'e) m =
      let l12 = List.combine l1 l2 in
      mapM (Tools.uncurry f) l12

    let iterM (f : ('a -> (unit, 'e) m)) (l : 'a list) : (unit, 'e) m = 
      let@ _ = mapM f l in 
      return ()

    let concat_mapM f l = 
      let@ xs = mapM f l in
      return (concat xs)

    let filter_mapM f l = 
      let@ xs = mapM f l in
      return (filter_map (fun x -> x) xs)

    let filterM f xs =
      let@ ys = mapM (fun x -> let@ b = f x in return (b, x)) xs in
      return (List.map snd (List.filter fst ys))


    let fold_leftM (f : 'a -> 'b -> ('c, 'e) m) (a : 'a) (bs : 'b list) =
      Stdlib.List.fold_left (fun aM b -> let@ a = aM in f a b) (return a) bs

    (* maybe from Exception.lem *)
    let fold_rightM (f : 'b -> 'a -> ('c, 'e) m) (bs : 'b list) (a : 'a) =
      Stdlib.List.fold_right (fun b aM -> let@ a = aM in f b a) bs (return a)

  end

  module PmapM = struct

    let foldM 
          (f : 'k -> 'x -> 'y -> ('y, 'e) m)
          (map : ('k,'x) Pmap.map) (init: 'y) : ('y, 'e) m =
      Pmap.fold (fun k v aM -> let@ a = aM in f k v a) map (return init)

    let iterM f m = 
      Pmap.fold (fun k v m -> let@ () = m in f k v) 
        m (return ())

    let mapM 
          (f: 'k -> 'v -> ('w, 'e) m)
          (m : ('k,'v) Pmap.map)
          (cmp: 'k -> 'k -> int)
        : (('k,'w) Pmap.map, 'e) m
      = 
      foldM (fun k v m -> 
          let@ v' = f k v in 
          return (Pmap.add k v' m)
        ) m (Pmap.empty cmp)

  end


end
