open BinPos
open Coqlib
open Datatypes
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type ITER = 
 sig 
  val iterate : ('a1 -> ('a2, 'a1) sum) -> 'a1 -> 'a2 option
 end

(** val dependent_description' : __ -> ('a1 -> 'a2, __) sigT **)

let dependent_description' = fun x -> assert false

module PrimIter = 
 struct 
  (** val num_iterations : positive **)
  
  let num_iterations =
    Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))))))))))))))))))))))))))))))))))
  
  (** val iter_step :
      ('a1 -> ('a2, 'a1) sum) -> positive -> (positive -> __ -> 'a1 -> 'a2
      option) -> 'a1 -> 'a2 option **)
  
  let iter_step step x next s =
    if peq x Coq_xH
    then None
    else (match step s with
            | Coq_inl res -> Some res
            | Coq_inr s' -> next (coq_Ppred x) __ s')
  
  (** val iter : ('a1 -> ('a2, 'a1) sum) -> positive -> 'a1 -> 'a2 option **)
  
  let rec iter step x =
    iter_step step x (fun y _ -> iter step y)
  
  (** val iterate : ('a1 -> ('a2, 'a1) sum) -> 'a1 -> 'a2 option **)
  
  let iterate step =
    iter step num_iterations
 end

module SafePrimIter = 
 struct 
  (** val iter_step :
      ('a1 -> ('a1, 'a1) sum) -> positive -> (positive -> __ -> 'a1 -> 'a1)
      -> 'a1 -> 'a1 **)
  
  let iter_step step x next s =
    if peq x Coq_xH
    then s
    else (match step s with
            | Coq_inl res -> res
            | Coq_inr s' -> next (coq_Ppred x) __ s')
  
  (** val iter : ('a1 -> ('a1, 'a1) sum) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter step x =
    iter_step step x (fun y _ -> iter step y)
  
  (** val num_iterations : positive **)
  
  let num_iterations =
    Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))))))))))))))))))))))))))))))))))
  
  (** val iterate : ('a1 -> ('a1, 'a1) sum) -> 'a1 -> 'a1 **)
  
  let iterate step =
    iter step num_iterations
 end

module GenIter = 
 struct 
  (** val coq_F_iter :
      ('a1 -> ('a2, 'a1) sum) -> ('a1 -> 'a2 option) -> 'a1 -> 'a2 option **)
  
  let coq_F_iter step next a =
    match step a with
      | Coq_inl b -> Some b
      | Coq_inr a' -> next a'
  
  (** val iter : ('a1 -> ('a2, 'a1) sum) -> nat -> 'a1 -> 'a2 option **)
  
  let rec iter step = function
    | O -> (fun a -> None)
    | S m -> coq_F_iter step (iter step m)
  
  (** val exists_iterate :
      ('a1 -> ('a2, 'a1) sum) -> ('a1 -> 'a2 option, __) sigT **)
  
  let exists_iterate step =
    dependent_description' __
  
  (** val iterate : ('a1 -> ('a2, 'a1) sum) -> 'a1 -> 'a2 option **)
  
  let iterate step =
    let Coq_existT (f, _) = exists_iterate step in f
 end

