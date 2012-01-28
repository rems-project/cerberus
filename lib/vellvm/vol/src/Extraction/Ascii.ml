open BinNat
open BinPos
open Bool
open Datatypes
open Nnat

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_rect :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    ascii -> 'a1 **)

let ascii_rect f = function
  | Ascii (x, x0, x1, x2, x3, x4, x5, x6) -> f x x0 x1 x2 x3 x4 x5 x6

(** val ascii_rec :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    ascii -> 'a1 **)

let ascii_rec f = function
  | Ascii (x, x0, x1, x2, x3, x4, x5, x6) -> f x x0 x1 x2 x3 x4 x5 x6

(** val zero : ascii **)

let zero =
  Ascii (false, false, false, false, false, false, false, false)

(** val one : ascii **)

let one =
  Ascii (true, false, false, false, false, false, false, false)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
  | Ascii (a1, a2, a3, a4, a5, a6, a7, a8) -> Ascii (c, a1, a2, a3, a4, a5,
      a6, a7)

(** val ascii_dec : ascii -> ascii -> bool **)

let ascii_dec a b =
  let Ascii (x, x0, x1, x2, x3, x4, x5, x6) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  if bool_dec x b8
  then if bool_dec x0 b9
       then if bool_dec x1 b10
            then if bool_dec x2 b11
                 then if bool_dec x3 b12
                      then if bool_dec x4 b13
                           then if bool_dec x5 b14
                                then bool_dec x6 b15
                                else false
                           else false
                      else false
                 else false
            else false
       else false
  else false

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n p =
    match n with
      | O -> zero
      | S n' ->
          (match p with
             | Coq_xI p' -> shift true (loop n' p')
             | Coq_xO p' -> shift false (loop n' p')
             | Coq_xH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : coq_N -> ascii **)

let ascii_of_N = function
  | N0 -> zero
  | Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> ascii **)

let ascii_of_nat a =
  ascii_of_N (coq_N_of_nat a)

(** val coq_N_of_digits : bool list -> coq_N **)

let rec coq_N_of_digits = function
  | [] -> N0
  | b::l' ->
      coq_Nplus (if b then Npos Coq_xH else N0)
        (coq_Nmult (Npos (Coq_xO Coq_xH)) (coq_N_of_digits l'))

(** val coq_N_of_ascii : ascii -> coq_N **)

let coq_N_of_ascii = function
  | Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
      coq_N_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[]))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  nat_of_N (coq_N_of_ascii a)

(** val coq_Space : ascii **)

let coq_Space =
  Ascii (false, false, false, false, false, true, false, false)

(** val coq_DoubleQuote : ascii **)

let coq_DoubleQuote =
  Ascii (false, true, false, false, false, true, false, false)

(** val coq_Beep : ascii **)

let coq_Beep =
  Ascii (true, true, true, false, false, false, false, false)

