open Bool
open Datatypes
open Peano_dec

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_EqDec = 'a -> 'a -> bool

(** val equiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let equiv_dec eqDec =
  eqDec

(** val swap_sumbool : bool -> bool **)

let swap_sumbool = function
  | true -> false
  | false -> true

(** val nequiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let nequiv_dec h x y =
  swap_sumbool (equiv_dec h x y)

(** val equiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let equiv_decb h x y =
  if equiv_dec h x y then true else false

(** val nequiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let nequiv_decb h x y =
  negb (equiv_decb h x y)

(** val nat_eq_eqdec : nat coq_EqDec **)

let nat_eq_eqdec =
  eq_nat_dec

(** val bool_eqdec : bool coq_EqDec **)

let bool_eqdec =
  bool_dec

(** val unit_eqdec : unit coq_EqDec **)

let unit_eqdec x y =
  true

(** val prod_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1*'a2) coq_EqDec **)

let prod_eqdec h h0 x y =
  let branch_0 = fun x1 x2 ->
    let branch_0 = fun y1 y2 ->
      if equiv_dec h x1 y1 then equiv_dec h0 x2 y2 else false
    in
    let y1,y2 = y in branch_0 y1 y2
  in
  let x1,x2 = x in branch_0 x1 x2

(** val sum_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) sum coq_EqDec **)

let sum_eqdec h h0 x y =
  let branch_0 = equiv_dec h in
  let branch_1 = equiv_dec h0 in
  let branch_2 = fun wildcard' wildcard'0 -> false in
  let branch_3 = fun wildcard' wildcard'0 -> false in
  (match x with
     | Coq_inl wildcard' ->
         (match y with
            | Coq_inl b -> branch_0 wildcard' b
            | Coq_inr wildcard'0 -> branch_2 wildcard' wildcard'0)
     | Coq_inr wildcard' ->
         (match y with
            | Coq_inl wildcard'0 -> branch_3 wildcard' wildcard'0
            | Coq_inr b -> branch_1 wildcard' b))

(** val bool_function_eqdec : 'a1 coq_EqDec -> (bool -> 'a1) coq_EqDec **)

let bool_function_eqdec h f g =
  if equiv_dec h (f true) (g true)
  then equiv_dec h (f false) (g false)
  else false

(** val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec **)

let rec list_eqdec eqa x y =
  let branch_0 = fun _ _ -> true in
  let branch_1 = fun hd tl hd' tl' ->
    if equiv_dec eqa hd hd' then list_eqdec eqa tl tl' else false
  in
  let branch_2 = fun wildcard' wildcard'0 -> false in
  (match x with
     | [] ->
         let wildcard' = [] in
         (match y with
            | [] -> branch_0 __ __
            | a::l -> let wildcard'0 = a::l in branch_2 wildcard' wildcard'0)
     | hd::tl ->
         let wildcard' = hd::tl in
         (match y with
            | [] -> let wildcard'0 = [] in branch_2 wildcard' wildcard'0
            | hd'::tl' -> branch_1 hd tl hd' tl'))

