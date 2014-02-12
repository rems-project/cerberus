open BinInt
open Datatypes
open ZOrderedType

type __ = Obj.t

val coq_Zmax : coq_Z -> coq_Z -> coq_Z

val coq_Zmin : coq_Z -> coq_Z -> coq_Z

module ZHasMinMax : 
 sig 
  val max : coq_Z -> coq_Z -> coq_Z
  
  val min : coq_Z -> coq_Z -> coq_Z
 end

module Z : 
 sig 
  module OT : 
   sig 
    type t = coq_Z
    
    val compare : coq_Z -> coq_Z -> comparison
    
    val eq_dec : coq_Z -> coq_Z -> bool
   end
  
  module T : 
   sig 
    
   end
  
  module ORev : 
   sig 
    type t = coq_Z
   end
  
  module MRev : 
   sig 
    val max : coq_Z -> coq_Z -> coq_Z
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
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1
    
    val max_case :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1
    
    val max_dec : coq_Z -> coq_Z -> bool
    
    val min_case_strong :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1
    
    val min_case :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1
    
    val min_dec : coq_Z -> coq_Z -> bool
   end
  
  val max_case_strong : coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : coq_Z -> coq_Z -> bool
  
  val min_case_strong : coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : coq_Z -> coq_Z -> bool
 end

