open Resultat

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
