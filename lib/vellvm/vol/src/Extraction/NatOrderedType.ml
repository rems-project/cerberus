open Compare_dec
open Datatypes
open EqNat
open Equalities
open OrdersTac

module Nat_as_UBE = 
 struct 
  type t = nat
  
  (** val eqb : nat -> nat -> bool **)
  
  let eqb =
    beq_nat
 end

module Nat_as_DT = Make_UDTF(Nat_as_UBE)

module Nat_as_OT = 
 struct 
  type t = nat
  
  (** val eqb : nat -> nat -> bool **)
  
  let eqb =
    beq_nat
  
  (** val eq_dec : nat -> nat -> bool **)
  
  let eq_dec x y =
    let b = beq_nat x y in if b then true else false
  
  (** val compare : nat -> nat -> comparison **)
  
  let compare =
    nat_compare
 end

module NatOrder = OTF_to_OrderTac(Nat_as_OT)

