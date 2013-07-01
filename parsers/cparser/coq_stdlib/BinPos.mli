open Datatypes
open Peano

type positive =
| Coq_xI of positive
| Coq_xO of positive
| Coq_xH

val positive_rect :
  (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive ->
  'a1

val positive_rec :
  (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive ->
  'a1

val coq_Psucc : positive -> positive

val coq_Pplus : positive -> positive -> positive

val coq_Pplus_carry : positive -> positive -> positive

val coq_Pmult_nat : positive -> nat -> nat

val nat_of_P : positive -> nat

val coq_P_of_succ_nat : nat -> positive

val coq_Pdouble_minus_one : positive -> positive

val coq_Ppred : positive -> positive

type positive_mask =
| IsNul
| IsPos of positive
| IsNeg

val positive_mask_rect :
  'a1 -> (positive -> 'a1) -> 'a1 -> positive_mask -> 'a1

val positive_mask_rec :
  'a1 -> (positive -> 'a1) -> 'a1 -> positive_mask -> 'a1

val coq_Pdouble_plus_one_mask : positive_mask -> positive_mask

val coq_Pdouble_mask : positive_mask -> positive_mask

val coq_Pdouble_minus_two : positive -> positive_mask

val coq_Pminus_mask : positive -> positive -> positive_mask

val coq_Pminus_mask_carry : positive -> positive -> positive_mask

val coq_Pminus : positive -> positive -> positive

val coq_Pmult : positive -> positive -> positive

val coq_Pdiv2 : positive -> positive

val coq_Pcompare : positive -> positive -> comparison -> comparison

val coq_Pmin : positive -> positive -> positive

val coq_Pmax : positive -> positive -> positive

val coq_Peqb : positive -> positive -> bool

val positive_eq_dec : positive -> positive -> bool

type coq_PeanoView =
| PeanoOne
| PeanoSucc of positive * coq_PeanoView

val coq_PeanoView_rect :
  'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
  coq_PeanoView -> 'a1

val coq_PeanoView_rec :
  'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
  coq_PeanoView -> 'a1

val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView

val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView

val peanoView : positive -> coq_PeanoView

val coq_PeanoView_iter :
  'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

val coq_Prect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

val coq_Prec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

val coq_Ppred_mask : positive_mask -> positive_mask

val coq_Psize : positive -> nat

