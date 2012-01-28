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

module Make : 
 functor (X:DecidableType.DecidableType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
   end
  
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type t = elt list
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val union : t -> t -> t
      
      val diff : t -> t -> t
      
      val inter : t -> t -> t
      
      val subset : t -> t -> bool
      
      val equal : t -> t -> bool
      
      val filter : (elt -> bool) -> t -> t
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val partition : (elt -> bool) -> t -> t*t
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val choose : t -> elt option
      
      val isok : elt list -> bool
     end
    
    module E : 
     sig 
      type t = X.t
      
      val eq_dec : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> t*t
    
    val eq_dec : t -> t -> bool
   end
  
  type elt = X.t
  
  type t = MSet.t
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
 end

