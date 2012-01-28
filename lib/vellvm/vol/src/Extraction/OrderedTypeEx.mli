open BinInt
open BinNat
open BinPos
open Compare_dec
open Datatypes
open Peano_dec
open ZArith_dec

module type UsualOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module UOT_to_OT : 
 functor (U:UsualOrderedType) ->
 sig 
  type t = U.t
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module Nat_as_OT : 
 sig 
  type t = nat
  
  val compare : t -> t -> nat OrderedType.coq_Compare
  
  val eq_dec : nat -> nat -> bool
 end

module Z_as_OT : 
 sig 
  type t = coq_Z
  
  val compare : coq_Z -> coq_Z -> coq_Z OrderedType.coq_Compare
  
  val eq_dec : coq_Z -> coq_Z -> bool
 end

module Positive_as_OT : 
 sig 
  type t = positive
  
  val compare : t -> t -> positive OrderedType.coq_Compare
  
  val eq_dec : positive -> positive -> bool
 end

module N_as_OT : 
 sig 
  type t = coq_N
  
  val compare : t -> t -> coq_N OrderedType.coq_Compare
  
  val eq_dec : coq_N -> coq_N -> bool
 end

module PairOrderedType : 
 functor (O1:OrderedType.OrderedType) ->
 functor (O2:OrderedType.OrderedType) ->
 sig 
  module MO1 : 
   sig 
    module OrderElts : 
     sig 
      type t = O1.t
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : O1.t -> O1.t -> bool
    
    val lt_dec : O1.t -> O1.t -> bool
    
    val eqb : O1.t -> O1.t -> bool
   end
  
  module MO2 : 
   sig 
    module OrderElts : 
     sig 
      type t = O2.t
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : O2.t -> O2.t -> bool
    
    val lt_dec : O2.t -> O2.t -> bool
    
    val eqb : O2.t -> O2.t -> bool
   end
  
  type t = O1.t*O2.t
  
  val compare : t -> t -> (O1.t*O2.t) OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module PositiveOrderedTypeBits : 
 sig 
  type t = positive
  
  val compare : t -> t -> positive OrderedType.coq_Compare
  
  val eq_dec : positive -> positive -> bool
 end

