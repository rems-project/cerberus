open BinNat
open BinPos
open Datatypes

type coq_Z =
  | Z0
  | Zpos of positive
  | Zneg of positive

(** val coq_Z_rect :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_rect f f0 f1 = function
  | Z0 -> f
  | Zpos x -> f0 x
  | Zneg x -> f1 x

(** val coq_Z_rec :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_rec f f0 f1 = function
  | Z0 -> f
  | Zpos x -> f0 x
  | Zneg x -> f1 x

(** val coq_Zdouble_plus_one : coq_Z -> coq_Z **)

let coq_Zdouble_plus_one = function
  | Z0 -> Zpos Coq_xH
  | Zpos p -> Zpos (Coq_xI p)
  | Zneg p -> Zneg (coq_Pdouble_minus_one p)

(** val coq_Zdouble_minus_one : coq_Z -> coq_Z **)

let coq_Zdouble_minus_one = function
  | Z0 -> Zneg Coq_xH
  | Zpos p -> Zpos (coq_Pdouble_minus_one p)
  | Zneg p -> Zneg (Coq_xI p)

(** val coq_Zdouble : coq_Z -> coq_Z **)

let coq_Zdouble = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_xO p)
  | Zneg p -> Zneg (Coq_xO p)

(** val coq_ZPminus : positive -> positive -> coq_Z **)

let rec coq_ZPminus x y =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q -> coq_Zdouble (coq_ZPminus p q)
           | Coq_xO q -> coq_Zdouble_plus_one (coq_ZPminus p q)
           | Coq_xH -> Zpos (Coq_xO p))
    | Coq_xO p ->
        (match y with
           | Coq_xI q -> coq_Zdouble_minus_one (coq_ZPminus p q)
           | Coq_xO q -> coq_Zdouble (coq_ZPminus p q)
           | Coq_xH -> Zpos (coq_Pdouble_minus_one p))
    | Coq_xH ->
        (match y with
           | Coq_xI q -> Zneg (Coq_xO q)
           | Coq_xO q -> Zneg (coq_Pdouble_minus_one q)
           | Coq_xH -> Z0)

(** val coq_Zplus : coq_Z -> coq_Z -> coq_Z **)

let coq_Zplus x y =
  match x with
    | Z0 -> y
    | Zpos x' ->
        (match y with
           | Z0 -> Zpos x'
           | Zpos y' -> Zpos (coq_Pplus x' y')
           | Zneg y' ->
               (match coq_Pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zneg (coq_Pminus y' x')
                  | Gt -> Zpos (coq_Pminus x' y')))
    | Zneg x' ->
        (match y with
           | Z0 -> Zneg x'
           | Zpos y' ->
               (match coq_Pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zpos (coq_Pminus y' x')
                  | Gt -> Zneg (coq_Pminus x' y'))
           | Zneg y' -> Zneg (coq_Pplus x' y'))

(** val coq_Zopp : coq_Z -> coq_Z **)

let coq_Zopp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

(** val coq_Zsucc : coq_Z -> coq_Z **)

let coq_Zsucc x =
  coq_Zplus x (Zpos Coq_xH)

(** val coq_Zpred : coq_Z -> coq_Z **)

let coq_Zpred x =
  coq_Zplus x (Zneg Coq_xH)

(** val coq_Zminus : coq_Z -> coq_Z -> coq_Z **)

let coq_Zminus m n =
  coq_Zplus m (coq_Zopp n)

(** val coq_Zmult : coq_Z -> coq_Z -> coq_Z **)

let coq_Zmult x y =
  match x with
    | Z0 -> Z0
    | Zpos x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zpos (coq_Pmult x' y')
           | Zneg y' -> Zneg (coq_Pmult x' y'))
    | Zneg x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zneg (coq_Pmult x' y')
           | Zneg y' -> Zpos (coq_Pmult x' y'))

(** val coq_Zcompare : coq_Z -> coq_Z -> comparison **)

let coq_Zcompare x y =
  match x with
    | Z0 -> (match y with
               | Z0 -> Eq
               | Zpos y' -> Lt
               | Zneg y' -> Gt)
    | Zpos x' ->
        (match y with
           | Zpos y' -> coq_Pcompare x' y' Eq
           | _ -> Gt)
    | Zneg x' ->
        (match y with
           | Zneg y' -> coq_CompOpp (coq_Pcompare x' y' Eq)
           | _ -> Lt)

(** val coq_Zsgn : coq_Z -> coq_Z **)

let coq_Zsgn = function
  | Z0 -> Z0
  | Zpos p -> Zpos Coq_xH
  | Zneg p -> Zneg Coq_xH

(** val coq_Zsucc' : coq_Z -> coq_Z **)

let coq_Zsucc' = function
  | Z0 -> Zpos Coq_xH
  | Zpos x' -> Zpos (coq_Psucc x')
  | Zneg x' -> coq_ZPminus Coq_xH x'

(** val coq_Zpred' : coq_Z -> coq_Z **)

let coq_Zpred' = function
  | Z0 -> Zneg Coq_xH
  | Zpos x' -> coq_ZPminus x' Coq_xH
  | Zneg x' -> Zneg (coq_Psucc x')

(** val coq_Zplus' : coq_Z -> coq_Z -> coq_Z **)

let coq_Zplus' x y =
  match x with
    | Z0 -> y
    | Zpos x' ->
        (match y with
           | Z0 -> x
           | Zpos y' -> Zpos (coq_Pplus x' y')
           | Zneg y' -> coq_ZPminus x' y')
    | Zneg x' ->
        (match y with
           | Z0 -> x
           | Zpos y' -> coq_ZPminus y' x'
           | Zneg y' -> Zneg (coq_Pplus x' y'))

(** val coq_Zabs_nat : coq_Z -> nat **)

let coq_Zabs_nat = function
  | Z0 -> O
  | Zpos p -> nat_of_P p
  | Zneg p -> nat_of_P p

(** val coq_Zabs : coq_Z -> coq_Z **)

let coq_Zabs = function
  | Zneg p -> Zpos p
  | x -> x

(** val coq_Z_of_nat : nat -> coq_Z **)

let coq_Z_of_nat = function
  | O -> Z0
  | S y -> Zpos (coq_P_of_succ_nat y)

(** val coq_Zabs_N : coq_Z -> coq_N **)

let coq_Zabs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p

(** val coq_Z_of_N : coq_N -> coq_Z **)

let coq_Z_of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

