open Resultat
open List

let rec mapM (f: 'a -> ('b,'e) result) (l: 'a list) : ('b list, 'e) result = 
  match l with
  | [] -> return []
  | x::xs -> 
     let* y = f x in
     let* ys = mapM f xs in
     return (y :: ys)

let iterM : ('a -> (unit,'e) result) -> 'a list -> (unit, 'e) result = 
  fun f l -> let* _ = mapM f l in return ()

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
