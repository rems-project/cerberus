open OrdersTac

type __ = Obj.t

type 'x coq_Compare =
| LT
| EQ
| GT

val coq_Compare_rect :
  'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1 coq_Compare
  -> 'a2

val coq_Compare_rec :
  'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1 coq_Compare
  -> 'a2

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

module MOT_to_OT : 
 functor (O:MiniOrderedType) ->
 sig 
  type t = O.t
  
  val compare : t -> t -> t coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts : 
 functor (O:OrderedType) ->
 sig 
  module OrderElts : 
   sig 
    type t = O.t
   end
  
  module OrderTac : 
   sig 
    
   end
  
  val eq_dec : O.t -> O.t -> bool
  
  val lt_dec : O.t -> O.t -> bool
  
  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType : 
 functor (O:OrderedType) ->
 sig 
  module MO : 
   sig 
    module OrderElts : 
     sig 
      type t = O.t
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : O.t -> O.t -> bool
    
    val lt_dec : O.t -> O.t -> bool
    
    val eqb : O.t -> O.t -> bool
   end
 end

