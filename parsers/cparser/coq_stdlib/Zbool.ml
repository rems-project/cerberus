open BinInt
open Datatypes
open Sumbool
open ZArith_dec
open Zeven

(** val coq_Z_lt_ge_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_ge_bool x y =
  bool_of_sumbool (coq_Z_lt_ge_dec x y)

(** val coq_Z_ge_lt_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_lt_bool x y =
  bool_of_sumbool (coq_Z_ge_lt_dec x y)

(** val coq_Z_le_gt_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_le_gt_bool x y =
  bool_of_sumbool (coq_Z_le_gt_dec x y)

(** val coq_Z_gt_le_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_le_bool x y =
  bool_of_sumbool (coq_Z_gt_le_dec x y)

(** val coq_Z_eq_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_eq_bool x y =
  bool_of_sumbool (coq_Z_eq_dec x y)

(** val coq_Z_noteq_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_noteq_bool x y =
  bool_of_sumbool (coq_Z_noteq_dec x y)

(** val coq_Zeven_odd_bool : coq_Z -> bool **)

let coq_Zeven_odd_bool x =
  bool_of_sumbool (coq_Zeven_odd_dec x)

(** val coq_Zle_bool : coq_Z -> coq_Z -> bool **)

let coq_Zle_bool x y =
  match coq_Zcompare x y with
  | Gt -> false
  | _ -> true

(** val coq_Zge_bool : coq_Z -> coq_Z -> bool **)

let coq_Zge_bool x y =
  match coq_Zcompare x y with
  | Lt -> false
  | _ -> true

(** val coq_Zlt_bool : coq_Z -> coq_Z -> bool **)

let coq_Zlt_bool x y =
  match coq_Zcompare x y with
  | Lt -> true
  | _ -> false

(** val coq_Zgt_bool : coq_Z -> coq_Z -> bool **)

let coq_Zgt_bool x y =
  match coq_Zcompare x y with
  | Gt -> true
  | _ -> false

(** val coq_Zeq_bool : coq_Z -> coq_Z -> bool **)

let coq_Zeq_bool x y =
  match coq_Zcompare x y with
  | Eq -> true
  | _ -> false

(** val coq_Zneq_bool : coq_Z -> coq_Z -> bool **)

let coq_Zneq_bool x y =
  match coq_Zcompare x y with
  | Eq -> false
  | _ -> true

(** val coq_Zle_bool_total : coq_Z -> coq_Z -> bool **)

let coq_Zle_bool_total x y =
  match coq_Zcompare x y with
  | Gt -> false
  | _ -> true

