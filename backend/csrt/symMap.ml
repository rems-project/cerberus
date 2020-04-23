open Except

include Map.Make(Sym)
let foldM 
      (f : key -> 'x -> 'y -> ('y,'e) m)
      (map : 'x t) (init: 'y) : ('y,'e) m =
  fold (fun k v a -> a >>= f k v) map (return init)
