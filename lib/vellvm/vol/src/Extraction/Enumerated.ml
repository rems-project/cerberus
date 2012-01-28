open Datatypes
open Peano

type 'u coq_U_list = 'u list

type 'u coq_U_enumerable = 'u coq_U_list

(** val coq_U_in_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 coq_U_list -> bool **)

let rec coq_U_in_dec u_separable x = function
  | [] -> false
  | y::l -> if u_separable x y then true else coq_U_in_dec u_separable x l

(** val coq_U_sum : ('a1 -> nat) -> 'a1 coq_U_list -> nat **)

let rec coq_U_sum f = function
  | [] -> O
  | x::ul' -> plus (f x) (coq_U_sum f ul')

(** val coq_U_enumerable_sum :
    ('a1 -> nat) -> 'a1 coq_U_enumerable -> nat **)

let coq_U_enumerable_sum f h =
  coq_U_sum f h

