open Datatypes
open NatOrderedType

type __ = Obj.t

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
    | O -> O
    | S n' -> (match m with
                 | O -> O
                 | S m' -> S (min n' m'))

module NatHasMinMax = 
 struct 
  (** val max : nat -> nat -> nat **)
  
  let max =
    max
  
  (** val min : nat -> nat -> nat **)
  
  let min =
    min
 end

module MMP = GenericMinMax.UsualMinMaxProperties(Nat_as_OT)(NatHasMinMax)

