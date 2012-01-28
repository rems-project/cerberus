open BinInt
open BinNat
open BinPos
open Datatypes
open OrderedTypeEx

module type UsualDecidableType = 
 Equalities.UsualDecidableTypeOrig

module UDT_to_DT : 
 functor (U:UsualDecidableType) ->
 sig 
  type t = U.t
  
  val eq_dec : t -> t -> bool
 end

module type MiniDecidableType = 
 Equalities.MiniDecidableType

module Make_UDT : 
 functor (M:MiniDecidableType) ->
 sig 
  type t = M.t
  
  val eq_dec : t -> t -> bool
 end

module OT_as_DT : 
 functor (O:OrderedType.OrderedType) ->
 sig 
  type t = O.t
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module Nat_as_DT : 
 sig 
  type t = nat
  
  val compare : t -> t -> nat OrderedType.coq_Compare
  
  val eq_dec : nat -> nat -> bool
 end

module Positive_as_DT : 
 sig 
  type t = positive
  
  val compare : t -> t -> positive OrderedType.coq_Compare
  
  val eq_dec : positive -> positive -> bool
 end

module N_as_DT : 
 sig 
  type t = coq_N
  
  val compare : t -> t -> coq_N OrderedType.coq_Compare
  
  val eq_dec : coq_N -> coq_N -> bool
 end

module Z_as_DT : 
 sig 
  type t = coq_Z
  
  val compare : coq_Z -> coq_Z -> coq_Z OrderedType.coq_Compare
  
  val eq_dec : coq_Z -> coq_Z -> bool
 end

module PairDecidableType : 
 functor (D1:DecidableType.DecidableType) ->
 functor (D2:DecidableType.DecidableType) ->
 sig 
  type t = D1.t*D2.t
  
  val eq_dec : (D1.t*D2.t) -> (D1.t*D2.t) -> bool
 end

module PairUsualDecidableType : 
 functor (D1:UsualDecidableType) ->
 functor (D2:UsualDecidableType) ->
 sig 
  type t = D1.t*D2.t
  
  val eq_dec : t -> t -> bool
 end

