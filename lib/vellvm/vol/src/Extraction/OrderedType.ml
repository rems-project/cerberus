open OrdersTac

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x coq_Compare =
  | LT
  | EQ
  | GT

(** val coq_Compare_rect :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
    coq_Compare -> 'a2 **)

let coq_Compare_rect x y f f0 f1 = function
  | LT -> f __
  | EQ -> f0 __
  | GT -> f1 __

(** val coq_Compare_rec :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
    coq_Compare -> 'a2 **)

let coq_Compare_rec x y f f0 f1 = function
  | LT -> f __
  | EQ -> f0 __
  | GT -> f1 __

module type MiniOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t coq_Compare
 end

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module MOT_to_OT = 
 functor (O:MiniOrderedType) ->
 struct 
  type t = O.t
  
  (** val compare : t -> t -> t coq_Compare **)
  
  let compare =
    O.compare
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    match compare x y with
      | EQ -> true
      | _ -> false
 end

module OrderedTypeFacts = 
 functor (O:OrderedType) ->
 struct 
  module OrderElts = 
   struct 
    type t = O.t
   end
  
  module OrderTac = MakeOrderTac(OrderElts)
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> bool **)
  
  let lt_dec x y =
    match O.compare x y with
      | LT -> true
      | _ -> false
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType = 
 functor (O:OrderedType) ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

