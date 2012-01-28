open BinInt
open BinPos
open Datatypes
open List0
open ZArith_dec
open Zdiv

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val peq : positive -> positive -> bool **)

let peq x y =
  match coq_Pcompare x y Eq with
    | Eq -> true
    | _ -> false

(** val plt : positive -> positive -> bool **)

let plt x y =
  coq_Z_lt_dec (Zpos x) (Zpos y)

(** val positive_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

let positive_rec v1 f =
  let iter = fun x p ->
    if peq x Coq_xH then v1 else f (coq_Ppred x) (p (coq_Ppred x) __)
  in
  (fun x -> let rec fix_F x0 =
              iter x0 (fun y _ -> fix_F y)
            in fix_F x)

(** val zeq : coq_Z -> coq_Z -> bool **)

let zeq =
  coq_Z_eq_dec

(** val zlt : coq_Z -> coq_Z -> bool **)

let zlt =
  coq_Z_lt_ge_dec

(** val zle : coq_Z -> coq_Z -> bool **)

let zle =
  coq_Z_le_gt_dec

(** val coq_Zdivide_dec : coq_Z -> coq_Z -> bool **)

let coq_Zdivide_dec p q =
  zeq (coq_Zmod q p) Z0

(** val nat_of_Z : coq_Z -> nat **)

let nat_of_Z = function
  | Zpos p -> nat_of_P p
  | _ -> O

(** val coq_ZRdiv : coq_Z -> coq_Z -> coq_Z **)

let coq_ZRdiv a b =
  if zeq (coq_Zmod a b) Z0
  then coq_Zdiv a b
  else coq_Zplus (coq_Zdiv a b) (Zpos Coq_xH)

(** val align : coq_Z -> coq_Z -> coq_Z **)

let align n amount =
  coq_Zmult (coq_Zdiv (coq_Zminus (coq_Zplus n amount) (Zpos Coq_xH)) amount)
    amount

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
  | Some y -> Some (f y)
  | None -> None

(** val sum_left_map : ('a1 -> 'a2) -> ('a1, 'a3) sum -> ('a2, 'a3) sum **)

let sum_left_map f = function
  | Coq_inl y -> Coq_inl (f y)
  | Coq_inr z -> Coq_inr z

(** val list_length_z_aux : 'a1 list -> coq_Z -> coq_Z **)

let rec list_length_z_aux l acc =
  match l with
    | [] -> acc
    | hd::tl -> list_length_z_aux tl (coq_Zsucc acc)

(** val list_length_z : 'a1 list -> coq_Z **)

let list_length_z l =
  list_length_z_aux l Z0

(** val list_nth_z : 'a1 list -> coq_Z -> 'a1 option **)

let rec list_nth_z l n =
  match l with
    | [] -> None
    | hd::tl -> if zeq n Z0 then Some hd else list_nth_z tl (coq_Zpred n)

(** val list_disjoint_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_disjoint_dec eqA_dec l1 l2 =
  match l1 with
    | [] -> true
    | y::l ->
        if in_dec eqA_dec y l2 then false else list_disjoint_dec eqA_dec l l2

(** val list_norepet_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec list_norepet_dec eqA_dec = function
  | [] -> true
  | y::l0 ->
      if list_norepet_dec eqA_dec l0
      then if in_dec eqA_dec y l0 then false else true
      else false

(** val list_drop : nat -> 'a1 list -> 'a1 list **)

let rec list_drop n x =
  match n with
    | O -> x
    | S n' -> (match x with
                 | [] -> []
                 | hd::tl -> list_drop n' tl)

(** val list_repeat : nat -> 'a1 -> 'a1 list **)

let rec list_repeat n x =
  match n with
    | O -> []
    | S m -> x::(list_repeat m x)

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
  | true -> true
  | false -> false

