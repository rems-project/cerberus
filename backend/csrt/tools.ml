module Loc = Locations

module StringMap = Map.Make(String)


let id = fun x -> x

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)


open Resultat

let at_most_one loc err_str = function
  | [] -> return None
  | [x] -> return (Some x)
  | _ -> fail loc (TypeErrors.Generic err_str)

let assoc_err loc entry list err =
  match List.assoc_opt entry list with
  | Some result -> return result
  | None -> fail loc err


