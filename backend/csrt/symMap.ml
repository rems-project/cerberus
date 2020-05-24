open Except

include Map.Make (
  struct 
    type t = Cerb_frontend.Symbol.sym 
    let compare = Cerb_frontend.Symbol.symbol_compare
  end
)

let foldM 
      (f : key -> 'x -> 'y -> ('y,'e) m)
      (map : 'x t) (init: 'y) : ('y,'e) m =
  fold (fun k v a -> let* a = a in f k v a) map (return init)
