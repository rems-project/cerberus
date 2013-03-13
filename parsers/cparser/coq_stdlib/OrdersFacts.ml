open Basics
open Datatypes
open Orders
open OrdersTac

module OrderedTypeFullFacts = 
 functor (O:OrderedTypeFull') ->
 struct 
  module OrderTac = OTF_to_OrderTac(O)
 end

module OrderedTypeFacts = 
 functor (O:OrderedType') ->
 struct 
  module OrderTac = OT_to_OrderTac(O)
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> bool **)
  
  let lt_dec x y =
    let c = coq_CompSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    if eq_dec x y then true else false
 end

module OrderedTypeTest = 
 functor (O:OrderedType') ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

module OrderedTypeRev = 
 functor (O:OrderedTypeFull) ->
 struct 
  type t = O.t
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val compare : O.t -> O.t -> comparison **)
  
  let compare =
    flip O.compare
 end

