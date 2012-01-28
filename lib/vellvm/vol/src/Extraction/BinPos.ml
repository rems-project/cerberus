open Datatypes
open Peano

type positive =
  | Coq_xI of positive
  | Coq_xO of positive
  | Coq_xH

(** val positive_rect :
    (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive
    -> 'a1 **)

let rec positive_rect f f0 f1 = function
  | Coq_xI p0 -> f p0 (positive_rect f f0 f1 p0)
  | Coq_xO p0 -> f0 p0 (positive_rect f f0 f1 p0)
  | Coq_xH -> f1

(** val positive_rec :
    (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive
    -> 'a1 **)

let rec positive_rec f f0 f1 = function
  | Coq_xI p0 -> f p0 (positive_rec f f0 f1 p0)
  | Coq_xO p0 -> f0 p0 (positive_rec f f0 f1 p0)
  | Coq_xH -> f1

(** val coq_Psucc : positive -> positive **)

let rec coq_Psucc = function
  | Coq_xI p -> Coq_xO (coq_Psucc p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

(** val coq_Pplus : positive -> positive -> positive **)

let rec coq_Pplus x y =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q -> Coq_xO (coq_Pplus_carry p q)
           | Coq_xO q -> Coq_xI (coq_Pplus p q)
           | Coq_xH -> Coq_xO (coq_Psucc p))
    | Coq_xO p ->
        (match y with
           | Coq_xI q -> Coq_xI (coq_Pplus p q)
           | Coq_xO q -> Coq_xO (coq_Pplus p q)
           | Coq_xH -> Coq_xI p)
    | Coq_xH ->
        (match y with
           | Coq_xI q -> Coq_xO (coq_Psucc q)
           | Coq_xO q -> Coq_xI q
           | Coq_xH -> Coq_xO Coq_xH)

(** val coq_Pplus_carry : positive -> positive -> positive **)

and coq_Pplus_carry x y =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q -> Coq_xI (coq_Pplus_carry p q)
           | Coq_xO q -> Coq_xO (coq_Pplus_carry p q)
           | Coq_xH -> Coq_xI (coq_Psucc p))
    | Coq_xO p ->
        (match y with
           | Coq_xI q -> Coq_xO (coq_Pplus_carry p q)
           | Coq_xO q -> Coq_xI (coq_Pplus p q)
           | Coq_xH -> Coq_xO (coq_Psucc p))
    | Coq_xH ->
        (match y with
           | Coq_xI q -> Coq_xI (coq_Psucc q)
           | Coq_xO q -> Coq_xO (coq_Psucc q)
           | Coq_xH -> Coq_xI Coq_xH)

(** val coq_Pmult_nat : positive -> nat -> nat **)

let rec coq_Pmult_nat x pow2 =
  match x with
    | Coq_xI p -> plus pow2 (coq_Pmult_nat p (plus pow2 pow2))
    | Coq_xO p -> coq_Pmult_nat p (plus pow2 pow2)
    | Coq_xH -> pow2

(** val nat_of_P : positive -> nat **)

let nat_of_P x =
  coq_Pmult_nat x (S O)

(** val coq_P_of_succ_nat : nat -> positive **)

let rec coq_P_of_succ_nat = function
  | O -> Coq_xH
  | S x -> coq_Psucc (coq_P_of_succ_nat x)

(** val coq_Pdouble_minus_one : positive -> positive **)

let rec coq_Pdouble_minus_one = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (coq_Pdouble_minus_one p)
  | Coq_xH -> Coq_xH

(** val coq_Ppred : positive -> positive **)

let coq_Ppred = function
  | Coq_xI p -> Coq_xO p
  | Coq_xO p -> coq_Pdouble_minus_one p
  | Coq_xH -> Coq_xH

type positive_mask =
  | IsNul
  | IsPos of positive
  | IsNeg

(** val positive_mask_rect :
    'a1 -> (positive -> 'a1) -> 'a1 -> positive_mask -> 'a1 **)

let positive_mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

(** val positive_mask_rec :
    'a1 -> (positive -> 'a1) -> 'a1 -> positive_mask -> 'a1 **)

let positive_mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

(** val coq_Pdouble_plus_one_mask : positive_mask -> positive_mask **)

let coq_Pdouble_plus_one_mask = function
  | IsNul -> IsPos Coq_xH
  | IsPos p -> IsPos (Coq_xI p)
  | IsNeg -> IsNeg

(** val coq_Pdouble_mask : positive_mask -> positive_mask **)

let coq_Pdouble_mask = function
  | IsPos p -> IsPos (Coq_xO p)
  | x0 -> x0

(** val coq_Pdouble_minus_two : positive -> positive_mask **)

let coq_Pdouble_minus_two = function
  | Coq_xI p -> IsPos (Coq_xO (Coq_xO p))
  | Coq_xO p -> IsPos (Coq_xO (coq_Pdouble_minus_one p))
  | Coq_xH -> IsNul

(** val coq_Pminus_mask : positive -> positive -> positive_mask **)

let rec coq_Pminus_mask x y =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q -> coq_Pdouble_mask (coq_Pminus_mask p q)
           | Coq_xO q -> coq_Pdouble_plus_one_mask (coq_Pminus_mask p q)
           | Coq_xH -> IsPos (Coq_xO p))
    | Coq_xO p ->
        (match y with
           | Coq_xI q ->
               coq_Pdouble_plus_one_mask (coq_Pminus_mask_carry p q)
           | Coq_xO q -> coq_Pdouble_mask (coq_Pminus_mask p q)
           | Coq_xH -> IsPos (coq_Pdouble_minus_one p))
    | Coq_xH -> (match y with
                   | Coq_xH -> IsNul
                   | _ -> IsNeg)

(** val coq_Pminus_mask_carry : positive -> positive -> positive_mask **)

and coq_Pminus_mask_carry x y =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q ->
               coq_Pdouble_plus_one_mask (coq_Pminus_mask_carry p q)
           | Coq_xO q -> coq_Pdouble_mask (coq_Pminus_mask p q)
           | Coq_xH -> IsPos (coq_Pdouble_minus_one p))
    | Coq_xO p ->
        (match y with
           | Coq_xI q -> coq_Pdouble_mask (coq_Pminus_mask_carry p q)
           | Coq_xO q ->
               coq_Pdouble_plus_one_mask (coq_Pminus_mask_carry p q)
           | Coq_xH -> coq_Pdouble_minus_two p)
    | Coq_xH -> IsNeg

(** val coq_Pminus : positive -> positive -> positive **)

let coq_Pminus x y =
  match coq_Pminus_mask x y with
    | IsPos z -> z
    | _ -> Coq_xH

(** val coq_Pmult : positive -> positive -> positive **)

let rec coq_Pmult x y =
  match x with
    | Coq_xI p -> coq_Pplus y (Coq_xO (coq_Pmult p y))
    | Coq_xO p -> Coq_xO (coq_Pmult p y)
    | Coq_xH -> y

(** val coq_Pdiv2 : positive -> positive **)

let coq_Pdiv2 = function
  | Coq_xI p -> p
  | Coq_xO p -> p
  | Coq_xH -> Coq_xH

(** val coq_Pcompare : positive -> positive -> comparison -> comparison **)

let rec coq_Pcompare x y r =
  match x with
    | Coq_xI p ->
        (match y with
           | Coq_xI q -> coq_Pcompare p q r
           | Coq_xO q -> coq_Pcompare p q Gt
           | Coq_xH -> Gt)
    | Coq_xO p ->
        (match y with
           | Coq_xI q -> coq_Pcompare p q Lt
           | Coq_xO q -> coq_Pcompare p q r
           | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                   | Coq_xH -> r
                   | _ -> Lt)

(** val coq_Pmin : positive -> positive -> positive **)

let coq_Pmin p p' =
  match coq_Pcompare p p' Eq with
    | Gt -> p'
    | _ -> p

(** val coq_Pmax : positive -> positive -> positive **)

let coq_Pmax p p' =
  match coq_Pcompare p p' Eq with
    | Gt -> p
    | _ -> p'

(** val coq_Peqb : positive -> positive -> bool **)

let rec coq_Peqb x y =
  match x with
    | Coq_xI p -> (match y with
                     | Coq_xI q -> coq_Peqb p q
                     | _ -> false)
    | Coq_xO p -> (match y with
                     | Coq_xO q -> coq_Peqb p q
                     | _ -> false)
    | Coq_xH -> (match y with
                   | Coq_xH -> true
                   | _ -> false)

(** val positive_eq_dec : positive -> positive -> bool **)

let rec positive_eq_dec p y0 =
  match p with
    | Coq_xI p0 ->
        (match y0 with
           | Coq_xI p1 -> positive_eq_dec p0 p1
           | _ -> false)
    | Coq_xO p0 ->
        (match y0 with
           | Coq_xO p1 -> positive_eq_dec p0 p1
           | _ -> false)
    | Coq_xH -> (match y0 with
                   | Coq_xH -> true
                   | _ -> false)

type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

(** val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1 **)

let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)

(** val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1 **)

let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)

(** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)

let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (Coq_xH, PeanoOne)
  | PeanoSucc (p0, q0) -> PeanoSucc ((coq_Psucc (Coq_xO p0)), (PeanoSucc
      ((Coq_xO p0), (peanoView_xO p0 q0))))

(** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)

let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((coq_Psucc Coq_xH), (PeanoSucc (Coq_xH,
      PeanoOne)))
  | PeanoSucc (p0, q0) -> PeanoSucc ((coq_Psucc (Coq_xI p0)), (PeanoSucc
      ((Coq_xI p0), (peanoView_xI p0 q0))))

(** val peanoView : positive -> coq_PeanoView **)

let rec peanoView = function
  | Coq_xI p0 -> peanoView_xI p0 (peanoView p0)
  | Coq_xO p0 -> peanoView_xO p0 (peanoView p0)
  | Coq_xH -> PeanoOne

(** val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)

(** val coq_Prect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

let coq_Prect a f p =
  coq_PeanoView_iter a f p (peanoView p)

(** val coq_Prec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

let coq_Prec =
  coq_Prect

(** val coq_Ppred_mask : positive_mask -> positive_mask **)

let coq_Ppred_mask = function
  | IsPos q -> (match q with
                  | Coq_xH -> IsNul
                  | _ -> IsPos (coq_Ppred q))
  | _ -> IsNeg

(** val coq_Psize : positive -> nat **)

let rec coq_Psize = function
  | Coq_xI p0 -> S (coq_Psize p0)
  | Coq_xO p0 -> S (coq_Psize p0)
  | Coq_xH -> S O

