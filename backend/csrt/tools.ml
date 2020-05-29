module CF = Cerb_frontend
module CB = Cerb_backend

module StringMap = Map.Make(String)

let uncurry f (a,b)  = f a b
let curry f a b = f (a,b)
let flip f a b = f b a


let concat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs



let precise_loc loc mlock = 
  match mlock with
  | Some loc2 -> loc2
  | None -> loc


let update_loc loc annots =
  precise_loc loc (CF.Annot.get_loc annots)
  
let aunpack loc (CF.Mucore.Annotated (annots, _, x)) = 
  (x, update_loc loc annots)



let make_substs
      (substitution_function : ('a,'b) Subst.t -> 'c -> 'c)
      (substs : (('a,'b) Subst.t) list)
      (c : 'c) : 'c 
  =
  List.fold_left (fun c substitution -> substitution_function substitution c)
    c substs



