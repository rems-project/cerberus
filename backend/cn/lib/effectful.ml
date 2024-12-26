module type S = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Make (T : S) = struct
  include T

  let ( let@ ) = T.bind

  module ListM = struct
    let rec mapM (f : 'a -> 'b t) (l : 'a list) : 'b list t =
      match l with
      | [] -> return []
      | x :: xs ->
        let@ y = f x in
        let@ ys = mapM f xs in
        return (y :: ys)


    let mapfstM (f : 'a -> 'c t) (l : ('a * 'b) list) : ('c * 'b) list t =
      mapM
        (fun (a, b) ->
          let@ c = f a in
          return (c, b))
        l


    let mapsndM (f : 'b -> 'c t) (l : ('a * 'b) list) : ('a * 'c) list t =
      mapM
        (fun (a, b) ->
          let@ c = f b in
          return (a, c))
        l


    let mapiM (f : int -> 'a -> 'b t) (l : 'a list) : 'b list t =
      let rec aux i l =
        match l with
        | [] -> return []
        | x :: xs ->
          let@ y = f i x in
          let@ ys = aux (i + 1) xs in
          return (y :: ys)
      in
      aux 0 l


    let map2M (f : 'a -> 'b -> 'c t) (l1 : 'a list) (l2 : 'b list) : 'c list t =
      let l12 = List.combine l1 l2 in
      mapM (Tools.uncurry f) l12


    let iteriM (f : int -> 'a -> unit t) (l : 'a list) : unit t =
      let@ _ = mapiM f l in
      return ()


    let iterM (f : 'a -> unit t) (l : 'a list) : unit t = iteriM (fun _ -> f) l

    let concat_mapM f l =
      let@ xs = mapM f l in
      return (List.concat xs)


    let filter_mapM f l =
      let@ xs = mapM f l in
      return (List.filter_map (fun x -> x) xs)


    let filterM f xs =
      let@ ys =
        mapM
          (fun x ->
            let@ b = f x in
            return (b, x))
          xs
      in
      return (List.map snd (List.filter fst ys))


    let fold_leftM (f : 'a -> 'b -> 'c t) (a : 'a) (bs : 'b list) =
      List.fold_left
        (fun aM b ->
          let@ a = aM in
          f a b)
        (return a)
        bs


    let fold_rightM (f : 'b -> 'a -> 'c t) (bs : 'b list) (a : 'a) =
      List.fold_right
        (fun b aM ->
          let@ a = aM in
          f b a)
        bs
        (return a)
  end

  module PmapM = struct
    let foldM (f : 'k -> 'x -> 'y -> 'y t) (map : ('k, 'x) Pmap.map) (init : 'y) : 'y t =
      Pmap.fold
        (fun k v aM ->
          let@ a = aM in
          f k v a)
        map
        (return init)


    let foldiM (f : int -> 'k -> 'x -> 'y -> 'y t) (map : ('k, 'x) Pmap.map) (init : 'y)
      : 'y t
      =
      ListM.fold_leftM
        (fun y (i, (k, x)) -> f i k x y)
        init
        (List.mapi (fun i (k, x) -> (i, (k, x))) (Pmap.bindings_list map))


    let iterM f m =
      Pmap.fold
        (fun k v m ->
          let@ () = m in
          f k v)
        m
        (return ())


    let mapM (f : 'k -> 'v -> 'w t) (m : ('k, 'v) Pmap.map) (cmp : 'k -> 'k -> int)
      : ('k, 'w) Pmap.map t
      =
      foldM
        (fun k v m ->
          let@ v' = f k v in
          return (Pmap.add k v' m))
        m
        (Pmap.empty cmp)
  end
end
