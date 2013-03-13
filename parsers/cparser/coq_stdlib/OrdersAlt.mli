open Datatypes

module type OrderedTypeOrig = 
 OrderedType.OrderedType

module type OrderedTypeAlt = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
 end

module Update_OT : 
 functor (O:OrderedTypeOrig) ->
 sig 
  type t = O.t
  
  val eq_dec : t -> t -> bool
  
  val compare : O.t -> O.t -> comparison
 end

module Backport_OT : 
 functor (O:Orders.OrderedType) ->
 sig 
  type t = O.t
  
  val eq_dec : t -> t -> bool
  
  val compare : O.t -> O.t -> O.t OrderedType.coq_Compare
 end

module OT_from_Alt : 
 functor (O:OrderedTypeAlt) ->
 sig 
  type t = O.t
  
  val compare : O.t -> O.t -> comparison
  
  val eq_dec : O.t -> O.t -> bool
 end

module OT_to_Alt : 
 functor (O:Orders.OrderedType) ->
 sig 
  type t = O.t
  
  val compare : O.t -> O.t -> comparison
 end

