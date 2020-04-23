open Printf
open Sexplib
open Except

let uncurry f (a,b)  = f a b
let curry f a b = f (a,b)
let flip f a b = f b a

type num = Nat_big_num.num


let sym_subst replace with_sym symbol = 
  if symbol = replace then with_sym else symbol


let parse_error (t : string) (sx : Sexp.t) (loc: Location.t) = 
  fail (sprintf "%s: unexpected %s: %s" (Location.pp loc) t (Sexp.to_string sx))

let concatmap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs

let list_of_maybe = function
  | None -> []
  | Some a -> [a]

let pp_list pp sep l = String.concat sep (List.map pp l)




let of_a a = 
  let (Cerb_frontend.Mucore.Annotated (_, _, x)) = a in x

let lof_a a = 
  let (Cerb_frontend.Mucore.Annotated (annots, _, x)) = a in 
  (x, Cerb_frontend.Annot.get_loc_ annots)
