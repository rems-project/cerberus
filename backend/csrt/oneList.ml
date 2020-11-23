(* non-empty lists *)

(* adapting https://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html *)
type 'a onelist =
  | Last of 'a
  | (::) of 'a * 'a onelist

type 'a t = 'a onelist

let rec to_list = function
  | Last a -> List.[a]
  | a :: r -> List.cons a (to_list r)

let head = function
  | Last a -> a
  | a :: _ -> a

let tail = function
  | Last a -> []
  | a :: r -> to_list r


let rec map (f : 'a -> 'b) (l : 'a onelist) : 'b onelist =
  match l with
  | Last a -> Last (f a)
  | a :: r -> f a :: map f r


let rec concat l1 l2 = 
  match l1 with
  | Last a -> a :: l2
  | a :: r -> a :: concat r l2
