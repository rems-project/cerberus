open Datatypes
open Int0
open MSetAVL
open OrdersAlt

module IntMake = 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 struct 
  module X' = Update_OT(X)
  
  module MSet = IntMake(I)(X')
  
  type elt = X.t
  
  type t = MSet.t
  
  (** val empty : t **)
  
  let empty =
    MSet.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty =
    MSet.is_empty
  
  (** val mem : elt -> t -> bool **)
  
  let mem =
    MSet.mem
  
  (** val add : elt -> t -> t **)
  
  let add =
    MSet.add
  
  (** val singleton : elt -> t **)
  
  let singleton =
    MSet.singleton
  
  (** val remove : elt -> t -> t **)
  
  let remove =
    MSet.remove
  
  (** val union : t -> t -> t **)
  
  let union =
    MSet.union
  
  (** val inter : t -> t -> t **)
  
  let inter =
    MSet.inter
  
  (** val diff : t -> t -> t **)
  
  let diff =
    MSet.diff
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    MSet.eq_dec
  
  (** val equal : t -> t -> bool **)
  
  let equal =
    MSet.equal
  
  (** val subset : t -> t -> bool **)
  
  let subset =
    MSet.subset
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold x x0 x1 =
    MSet.fold x x0 x1
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all =
    MSet.for_all
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ =
    MSet.exists_
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter =
    MSet.filter
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition =
    MSet.partition
  
  (** val cardinal : t -> nat **)
  
  let cardinal =
    MSet.cardinal
  
  (** val elements : t -> elt list **)
  
  let elements =
    MSet.elements
  
  (** val choose : t -> elt option **)
  
  let choose =
    MSet.choose
  
  module MF = 
   struct 
    (** val eqb : X.t -> X.t -> bool **)
    
    let eqb x y =
      if MSet.E.eq_dec x y then true else false
   end
  
  (** val min_elt : t -> elt option **)
  
  let min_elt =
    MSet.min_elt
  
  (** val max_elt : t -> elt option **)
  
  let max_elt =
    MSet.max_elt
  
  (** val compare : t -> t -> t OrderedType.coq_Compare **)
  
  let compare s s' =
    let c = coq_CompSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> OrderedType.EQ
     | CompLtT -> OrderedType.LT
     | CompGtT -> OrderedType.GT)
  
  module E = 
   struct 
    type t = X.t
    
    (** val compare : t -> t -> t OrderedType.coq_Compare **)
    
    let compare =
      X.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
 end

module Make = 
 functor (X:OrderedType.OrderedType) ->
 IntMake(Z_as_Int)(X)

