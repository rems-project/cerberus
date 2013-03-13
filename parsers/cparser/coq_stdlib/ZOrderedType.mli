open BinInt
open Datatypes
open Equalities
open OrdersTac
open Zbool

module Z_as_UBE : 
 sig 
  type t = coq_Z
  
  val eqb : coq_Z -> coq_Z -> bool
 end

module Z_as_DT : 
 sig 
  type t = coq_Z
  
  val eqb : coq_Z -> coq_Z -> bool
  
  val eq_dec : coq_Z -> coq_Z -> bool
 end

module Z_as_OT : 
 sig 
  type t = coq_Z
  
  val eqb : coq_Z -> coq_Z -> bool
  
  val eq_dec : coq_Z -> coq_Z -> bool
  
  val compare : coq_Z -> coq_Z -> comparison
 end

module ZOrder : 
 sig 
  module TO : 
   sig 
    type t = coq_Z
    
    val compare : coq_Z -> coq_Z -> comparison
    
    val eq_dec : coq_Z -> coq_Z -> bool
   end
 end

