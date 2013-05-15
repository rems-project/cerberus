open Datatypes

module type OrderedTypeOrig = 
 OrderedType.OrderedType

module type OrderedTypeAlt = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
 end

module Update_OT = 
 functor (O:OrderedTypeOrig) ->
 struct 
  type t = O.t
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val compare : O.t -> O.t -> comparison **)
  
  let compare x y =
    match O.compare x y with
    | OrderedType.LT -> Lt
    | OrderedType.EQ -> Eq
    | OrderedType.GT -> Gt
 end

module Backport_OT = 
 functor (O:Orders.OrderedType) ->
 struct 
  type t = O.t
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val compare : O.t -> O.t -> O.t OrderedType.coq_Compare **)
  
  let compare x y =
    let c = coq_CompSpec2Type x y (O.compare x y) in
    (match c with
     | CompEqT -> OrderedType.EQ
     | CompLtT -> OrderedType.LT
     | CompGtT -> OrderedType.GT)
 end

module OT_from_Alt = 
 functor (O:OrderedTypeAlt) ->
 struct 
  type t = O.t
  
  (** val compare : O.t -> O.t -> comparison **)
  
  let compare =
    O.compare
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false
 end

module OT_to_Alt = 
 functor (O:Orders.OrderedType) ->
 struct 
  type t = O.t
  
  (** val compare : O.t -> O.t -> comparison **)
  
  let compare =
    O.compare
 end

