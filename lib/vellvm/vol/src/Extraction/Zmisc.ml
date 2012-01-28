open BinInt
open BinPos

(** val iter_pos : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_pos n f x =
  match n with
    | Coq_xI n' -> f (iter_pos n' f (iter_pos n' f x))
    | Coq_xO n' -> iter_pos n' f (iter_pos n' f x)
    | Coq_xH -> f x

(** val iter : coq_Z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let iter n f x =
  match n with
    | Zpos p -> iter_pos p f x
    | _ -> x

