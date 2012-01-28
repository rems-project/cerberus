open BinNat
open BinPos
open Bool
open Datatypes
open Nnat

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_rect :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  ascii -> 'a1

val ascii_rec :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  ascii -> 'a1

val zero : ascii

val one : ascii

val shift : bool -> ascii -> ascii

val ascii_dec : ascii -> ascii -> bool

val ascii_of_pos : positive -> ascii

val ascii_of_N : coq_N -> ascii

val ascii_of_nat : nat -> ascii

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : ascii -> coq_N

val nat_of_ascii : ascii -> nat

val coq_Space : ascii

val coq_DoubleQuote : ascii

val coq_Beep : ascii

