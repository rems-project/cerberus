open Compare_dec
open Datatypes
open EqNat
open Equalities
open OrdersTac

module Nat_as_UBE : 
 sig 
  type t = nat
  
  val eqb : nat -> nat -> bool
 end

module Nat_as_DT : 
 sig 
  type t = nat
  
  val eqb : nat -> nat -> bool
  
  val eq_dec : nat -> nat -> bool
 end

module Nat_as_OT : 
 sig 
  type t = nat
  
  val eqb : nat -> nat -> bool
  
  val eq_dec : nat -> nat -> bool
  
  val compare : nat -> nat -> comparison
 end

module NatOrder : 
 sig 
  module TO : 
   sig 
    type t = nat
    
    val compare : nat -> nat -> comparison
    
    val eq_dec : nat -> nat -> bool
   end
 end

