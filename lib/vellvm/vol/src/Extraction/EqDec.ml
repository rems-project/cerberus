open Datatypes

type 'a dec_eq = bool

type 'a coq_EqDec = 'a -> 'a -> bool

(** val eq_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let eq_dec eqDec =
  eqDec

(** val nat_eqdec : nat coq_EqDec **)

let rec nat_eqdec n y0 =
  match n with
    | O -> (match y0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match y0 with
                 | O -> false
                 | S n1 -> nat_eqdec n0 n1)

(** val bool_eqdec : bool coq_EqDec **)

let bool_eqdec x y =
  if x then if y then true else false else if y then false else true

(** val unit_eqdec : unit coq_EqDec **)

let unit_eqdec x y =
  true

(** val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec **)

let rec list_eqdec h x y =
  match x with
    | [] -> (match y with
               | [] -> true
               | a::l -> false)
    | y0::l ->
        (match y with
           | [] -> false
           | a0::l0 -> if h y0 a0 then list_eqdec h l l0 else false)

(** val coq_K_dec : 'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2 **)

let coq_K_dec h x x0 =
  x0

