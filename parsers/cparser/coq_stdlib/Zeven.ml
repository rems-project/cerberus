open BinInt
open BinPos
open Datatypes

(** val coq_Zeven_bool : coq_Z -> bool **)

let coq_Zeven_bool = function
| Z0 -> true
| Zpos p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)

(** val coq_Zodd_bool : coq_Z -> bool **)

let coq_Zodd_bool = function
| Z0 -> false
| Zpos p ->
  (match p with
   | Coq_xO p0 -> false
   | _ -> true)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> false
   | _ -> true)

(** val coq_Zeven_odd_dec : coq_Z -> bool **)

let coq_Zeven_odd_dec = function
| Z0 -> true
| Zpos p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)

(** val coq_Zeven_dec : coq_Z -> bool **)

let coq_Zeven_dec = function
| Z0 -> true
| Zpos p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)

(** val coq_Zodd_dec : coq_Z -> bool **)

let coq_Zodd_dec = function
| Z0 -> false
| Zpos p ->
  (match p with
   | Coq_xO p0 -> false
   | _ -> true)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> false
   | _ -> true)

(** val coq_Zdiv2 : coq_Z -> coq_Z **)

let coq_Zdiv2 = function
| Z0 -> Z0
| Zpos p ->
  (match p with
   | Coq_xH -> Z0
   | _ -> Zpos (coq_Pdiv2 p))
| Zneg p ->
  (match p with
   | Coq_xH -> Z0
   | _ -> Zneg (coq_Pdiv2 p))

(** val coq_Z_modulo_2 : coq_Z -> (coq_Z, coq_Z) sum **)

let coq_Z_modulo_2 x =
  if coq_Zeven_odd_dec x
  then Coq_inl (coq_Zdiv2 x)
  else Coq_inr
         (match x with
          | Z0 -> assert false (* absurd case *)
          | Zpos p -> coq_Zdiv2 (Zpos p)
          | Zneg p -> coq_Zdiv2 (coq_Zpred (Zneg p)))

(** val coq_Zsplit2 : coq_Z -> (coq_Z, coq_Z) prod **)

let coq_Zsplit2 x =
  match coq_Z_modulo_2 x with
  | Coq_inl x0 -> Coq_pair (x0, x0)
  | Coq_inr x0 -> Coq_pair (x0, (coq_Zplus x0 (Zpos Coq_xH)))

