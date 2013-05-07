open BinInt
open BinPos
open Datatypes
open Specif
open Sumbool

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Dcompare_inf : comparison -> bool sumor **)

let coq_Dcompare_inf = function
| Eq -> Coq_inleft true
| Lt -> Coq_inleft false
| Gt -> Coq_inright

(** val coq_Zcompare_rect :
    coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let coq_Zcompare_rect n m h1 h2 h3 =
  let c = coq_Zcompare n m in
  (match c with
   | Eq -> h1 __
   | Lt -> h2 __
   | Gt -> h3 __)

(** val coq_Zcompare_rec :
    coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let coq_Zcompare_rec =
  coq_Zcompare_rect

(** val coq_Z_eq_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_eq_dec x y =
  match x with
  | Z0 ->
    (match y with
     | Z0 -> true
     | _ -> false)
  | Zpos x0 ->
    (match y with
     | Zpos p0 -> positive_eq_dec x0 p0
     | _ -> false)
  | Zneg x0 ->
    (match y with
     | Zneg p0 -> positive_eq_dec x0 p0
     | _ -> false)

(** val coq_Z_lt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_dec x y =
  coq_Zcompare_rec x y (fun _ -> false) (fun _ -> true) (fun _ -> false)

(** val coq_Z_le_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_le_dec x y =
  coq_Zcompare_rec x y (fun _ -> true) (fun _ -> true) (fun _ -> false)

(** val coq_Z_gt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_dec x y =
  coq_Zcompare_rec x y (fun _ -> false) (fun _ -> false) (fun _ -> true)

(** val coq_Z_ge_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_dec x y =
  coq_Zcompare_rec x y (fun _ -> true) (fun _ -> false) (fun _ -> true)

(** val coq_Z_lt_ge_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_ge_dec x y =
  coq_Z_lt_dec x y

(** val coq_Z_lt_le_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_le_dec x y =
  coq_Z_lt_ge_dec x y

(** val coq_Z_le_gt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_le_gt_dec x y =
  coq_Z_le_dec x y

(** val coq_Z_gt_le_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_le_dec x y =
  coq_Z_gt_dec x y

(** val coq_Z_ge_lt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_lt_dec x y =
  coq_Z_ge_dec x y

(** val coq_Z_le_lt_eq_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_le_lt_eq_dec x y =
  coq_Zcompare_rec x y (fun _ -> false) (fun _ -> true) (fun _ ->
    assert false (* absurd case *))

(** val coq_Zlt_cotrans : coq_Z -> coq_Z -> coq_Z -> bool **)

let coq_Zlt_cotrans x y z =
  coq_Z_lt_ge_dec x z

(** val coq_Zlt_cotrans_pos : coq_Z -> coq_Z -> bool **)

let coq_Zlt_cotrans_pos x y =
  coq_Zlt_cotrans Z0 (coq_Zplus x y) x

(** val coq_Zlt_cotrans_neg : coq_Z -> coq_Z -> bool **)

let coq_Zlt_cotrans_neg x y =
  if coq_Zlt_cotrans (coq_Zplus x y) Z0 x then false else true

(** val not_Zeq_inf : coq_Z -> coq_Z -> bool **)

let not_Zeq_inf x y =
  if coq_Z_lt_ge_dec x y
  then true
  else if coq_Z_le_lt_eq_dec y x
       then false
       else assert false (* absurd case *)

(** val coq_Z_dec : coq_Z -> coq_Z -> bool sumor **)

let coq_Z_dec x y =
  if coq_Z_lt_ge_dec x y
  then Coq_inleft true
  else if coq_Z_le_lt_eq_dec y x then Coq_inleft false else Coq_inright

(** val coq_Z_dec' : coq_Z -> coq_Z -> bool sumor **)

let coq_Z_dec' x y =
  if coq_Z_eq_dec x y then Coq_inright else Coq_inleft (not_Zeq_inf x y)

(** val coq_Z_zerop : coq_Z -> bool **)

let coq_Z_zerop x =
  coq_Z_eq_dec x Z0

(** val coq_Z_notzerop : coq_Z -> bool **)

let coq_Z_notzerop x =
  sumbool_not (coq_Z_zerop x)

(** val coq_Z_noteq_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_noteq_dec x y =
  sumbool_not (coq_Z_eq_dec x y)

