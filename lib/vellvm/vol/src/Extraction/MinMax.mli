open Datatypes
open NatOrderedType

type __ = Obj.t

val max : nat -> nat -> nat

val min : nat -> nat -> nat

module NatHasMinMax : 
 sig 
  val max : nat -> nat -> nat
  
  val min : nat -> nat -> nat
 end

module MMP : 
 sig 
  module OT : 
   sig 
    type t = nat
    
    val compare : nat -> nat -> comparison
    
    val eq_dec : nat -> nat -> bool
   end
  
  module T : 
   sig 
    
   end
  
  module ORev : 
   sig 
    type t = nat
   end
  
  module MRev : 
   sig 
    val max : nat -> nat -> nat
   end
  
  module MPRev : 
   sig 
    module T : 
     sig 
      
     end
   end
  
  module P : 
   sig 
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : nat -> nat -> bool
    
    val min_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val min_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : nat -> nat -> bool
   end
  
  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : nat -> nat -> bool
  
  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : nat -> nat -> bool
 end

