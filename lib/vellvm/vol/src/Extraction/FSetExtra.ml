open Datatypes
open MSetWeakList

module type WSfun = 
 functor (X:DecidableType.DecidableType) ->
 sig 
  type elt = X.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : X.t -> t -> bool
  
  val add : X.t -> t -> t
  
  val singleton : X.t -> t
  
  val remove : X.t -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (X.t -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (X.t -> bool) -> t -> bool
  
  val exists_ : (X.t -> bool) -> t -> bool
  
  val filter : (X.t -> bool) -> t -> t
  
  val partition : (X.t -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> X.t list
  
  val choose : t -> X.t option
 end

module Make = 
 functor (X:DecidableType.DecidableType) ->
 struct 
  module E = 
   struct 
    type t = X.t
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  module X' = 
   struct 
    type t = X.t
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  module MSet = Make(X')
  
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
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
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
 end

