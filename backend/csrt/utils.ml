open Cerb_frontend

module StringMap = Map.Make(String)

let uncurry f (a,b)  = f a b
let curry f a b = f (a,b)
let flip f a b = f b a

type num = Nat_big_num.num


let concat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs


let pp_list pp sep l = String.concat sep (List.map pp l)



let precise_loc loc mlock = 
  match mlock with
  | Some loc2 -> loc2
  | None -> loc


let update_loc loc annots =
  precise_loc loc (Annot.get_loc annots)
  
let aunpack loc (Mucore.Annotated (annots, _, x)) = 
  (x, update_loc loc annots)




