module type S = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end



module Make(T : S) = struct

  open T

  let (let@) = T.bind




  module ListM = struct

    let rec mapM (f : 'a -> 'b m) (l : 'a list) : ('b list) m =
      match l with
      | [] -> return []
      | x :: xs ->
         let@ y = f x in
         let@ ys = mapM f xs in
         return (y :: ys)

    let mapfstM (f : 'a -> 'c m) (l : ('a * 'b) list) : (('c * 'b) list) m =
      mapM (fun (a, b) -> let@ c = f a in return (c, b)) l

    let mapsndM (f : 'b -> 'c m) (l : ('a * 'b) list) : (('a * 'c) list) m =
      mapM (fun (a, b) -> let@ c = f b in return (a, c)) l



    let mapiM (f : int -> 'a -> 'b m)
              (l : 'a list) : ('b list) m =
      let rec aux i l =
        match l with
        | [] -> return []
        | x :: xs ->
           let@ y = f i x in
           let@ ys = aux (i + 1) xs in
           return (y :: ys)
      in
      aux 0 l

    let map2M (f : 'a -> 'b -> 'c m)
              (l1 : 'a list)
              (l2 : 'b list)
            : ('c list) m =
      let l12 = List.Old.combine l1 l2 in
      mapM (Tools.uncurry f) l12

    let iteriM (f : (int -> 'a -> unit m)) (l : 'a list) : unit m =
      let@ _ = mapiM f l in
      return ()

    let iterM (f : ('a -> unit m)) (l : 'a list) : unit m =
      iteriM (fun _ -> f) l

    let concat_mapM f l =
      let@ xs = mapM f l in
      return (List.concat xs)

    let filter_mapM f l =
      let@ xs = mapM f l in
      return (List.Old.filter_map (fun x -> x) xs)

    let filterM f xs =
      let@ ys = mapM (fun x -> let@ b = f x in return (b, x)) xs in
      return (List.map ~f:snd (List.Old.filter fst ys))


    let fold_leftM (f : 'a -> 'b -> 'c m) (a : 'a) (bs : 'b list) =
      List.Old.fold_left (fun aM b -> let@ a = aM in f a b) (return a) bs

    (* maybe from Exception.lem *)
    let fold_rightM (f : 'b -> 'a -> 'c m) (bs : 'b list) (a : 'a) =
      List.Old.fold_right (fun b aM -> let@ a = aM in f b a) bs (return a)

  end

  module PmapM = struct

    let foldM
          (f : 'k -> 'x -> 'y -> 'y m)
          (map : ('k,'x) Pmap.map) (init: 'y) : 'y m =
      Pmap.fold (fun k v aM -> let@ a = aM in f k v a) map (return init)

    let foldiM
          (f : int -> 'k -> 'x -> 'y -> 'y m)
          (map : ('k,'x) Pmap.map) (init: 'y) : 'y m =
      ListM.fold_leftM (fun y (i, (k, x)) -> f i k x y)
          init
          (List.Old.mapi (fun i (k, x) -> (i, (k, x))) (Pmap.bindings_list map))

    let iterM f m =
      Pmap.fold (fun k v m -> let@ () = m in f k v)
        m (return ())

    let mapM
          (f: 'k -> 'v -> 'w m)
          (m : ('k,'v) Pmap.map)
          (cmp: 'k -> 'k -> int)
        : (('k,'w) Pmap.map) m
      =
      foldM (fun k v m ->
          let@ v' = f k v in
          return (Pmap.add k v' m)
        ) m (Pmap.empty cmp)

  end


end
