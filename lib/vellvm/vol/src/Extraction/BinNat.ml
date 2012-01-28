open BinPos
open Datatypes
open Specif

type coq_N =
  | N0
  | Npos of positive

(** val coq_N_rect : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1 **)

let coq_N_rect f f0 = function
  | N0 -> f
  | Npos x -> f0 x

(** val coq_N_rec : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1 **)

let coq_N_rec f f0 = function
  | N0 -> f
  | Npos x -> f0 x

(** val coq_Ndiscr : coq_N -> positive sumor **)

let coq_Ndiscr = function
  | N0 -> Coq_inright
  | Npos p -> Coq_inleft p

(** val coq_Ndouble_plus_one : coq_N -> coq_N **)

let coq_Ndouble_plus_one = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

(** val coq_Ndouble : coq_N -> coq_N **)

let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

(** val coq_Nsucc : coq_N -> coq_N **)

let coq_Nsucc = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (coq_Psucc p)

(** val coq_Npred : coq_N -> coq_N **)

let coq_Npred = function
  | N0 -> N0
  | Npos p -> (match p with
                 | Coq_xH -> N0
                 | _ -> Npos (coq_Ppred p))

(** val coq_Nplus : coq_N -> coq_N -> coq_N **)

let coq_Nplus n m =
  match n with
    | N0 -> m
    | Npos p -> (match m with
                   | N0 -> n
                   | Npos q -> Npos (coq_Pplus p q))

(** val coq_Nminus : coq_N -> coq_N -> coq_N **)

let coq_Nminus n m =
  match n with
    | N0 -> N0
    | Npos n' ->
        (match m with
           | N0 -> n
           | Npos m' ->
               (match coq_Pminus_mask n' m' with
                  | IsPos p -> Npos p
                  | _ -> N0))

(** val coq_Nmult : coq_N -> coq_N -> coq_N **)

let coq_Nmult n m =
  match n with
    | N0 -> N0
    | Npos p -> (match m with
                   | N0 -> N0
                   | Npos q -> Npos (coq_Pmult p q))

(** val coq_Neqb : coq_N -> coq_N -> bool **)

let coq_Neqb n m =
  match n with
    | N0 -> (match m with
               | N0 -> true
               | Npos p -> false)
    | Npos n0 -> (match m with
                    | N0 -> false
                    | Npos m0 -> coq_Peqb n0 m0)

(** val coq_Ncompare : coq_N -> coq_N -> comparison **)

let coq_Ncompare n m =
  match n with
    | N0 -> (match m with
               | N0 -> Eq
               | Npos m' -> Lt)
    | Npos n' ->
        (match m with
           | N0 -> Gt
           | Npos m' -> coq_Pcompare n' m' Eq)

(** val coq_Nmin : coq_N -> coq_N -> coq_N **)

let coq_Nmin n n' =
  match coq_Ncompare n n' with
    | Gt -> n'
    | _ -> n

(** val coq_Nmax : coq_N -> coq_N -> coq_N **)

let coq_Nmax n n' =
  match coq_Ncompare n n' with
    | Gt -> n
    | _ -> n'

(** val coq_N_eq_dec : coq_N -> coq_N -> bool **)

let coq_N_eq_dec n m =
  match n with
    | N0 -> (match m with
               | N0 -> true
               | Npos p -> false)
    | Npos x ->
        (match m with
           | N0 -> false
           | Npos p0 -> positive_eq_dec x p0)

(** val coq_N_rec_double :
    coq_N -> 'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> 'a1 **)

let coq_N_rec_double a h h0 h1 =
  match a with
    | N0 -> h
    | Npos x ->
        let rec f = function
          | Coq_xI p0 -> h1 (Npos p0) (f p0)
          | Coq_xO p0 -> h0 (Npos p0) (f p0)
          | Coq_xH -> h1 N0 h
        in f x

(** val coq_Nrect : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

let coq_Nrect a f n =
  let f' = fun p x -> f (Npos p) x in
  (match n with
     | N0 -> a
     | Npos p -> coq_Prect (f N0 a) f' p)

(** val coq_Nrec : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

let coq_Nrec =
  coq_Nrect

(** val coq_Ndiv2 : coq_N -> coq_N **)

let coq_Ndiv2 = function
  | N0 -> N0
  | Npos p0 ->
      (match p0 with
         | Coq_xI p -> Npos p
         | Coq_xO p -> Npos p
         | Coq_xH -> N0)

