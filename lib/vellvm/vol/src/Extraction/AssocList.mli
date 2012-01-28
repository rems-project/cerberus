open CoqFSetDecide
open Datatypes
open DecidableTypeEx
open FSetFacts
open FSetProperties
open List0

type __ = Obj.t

module Make : 
 functor (X:UsualDecidableType) ->
 functor (KeySet:sig 
  type elt = X.t
  
  type t 
  
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
 end) ->
 sig 
  module D : 
   sig 
    module F : 
     sig 
      val eqb : X.t -> X.t -> bool
     end
    
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  module KeySetProperties : 
   sig 
    module Dec : 
     sig 
      module F : 
       sig 
        val eqb : X.t -> X.t -> bool
       end
      
      module FSetLogicalFacts : 
       sig 
        
       end
      
      module FSetDecideAuxiliary : 
       sig 
        
       end
      
      module FSetDecideTestCases : 
       sig 
        
       end
     end
    
    module FM : 
     sig 
      val eqb : X.t -> X.t -> bool
     end
    
    val coq_In_dec : KeySet.elt -> KeySet.t -> bool
    
    val of_list : KeySet.elt list -> KeySet.t
    
    val to_list : KeySet.t -> KeySet.elt list
    
    val fold_rec :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> (KeySet.t -> __ ->
      'a2) -> (KeySet.elt -> 'a1 -> KeySet.t -> KeySet.t -> __ -> __ -> __ ->
      'a2 -> 'a2) -> 'a2
    
    val fold_rec_bis :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> (KeySet.t -> KeySet.t
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KeySet.elt -> 'a1 -> KeySet.t ->
      __ -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_nodep :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> 'a2 -> (KeySet.elt ->
      'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> (KeySet.t -> KeySet.t -> 'a1 -> __
      -> 'a2 -> 'a2) -> 'a2 -> (KeySet.elt -> 'a1 -> KeySet.t -> __ -> 'a2 ->
      'a2) -> KeySet.t -> 'a2
    
    val fold_rel :
      (KeySet.elt -> 'a1 -> 'a1) -> (KeySet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
      -> KeySet.t -> 'a3 -> (KeySet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
      'a3
    
    val set_induction :
      (KeySet.t -> __ -> 'a1) -> (KeySet.t -> KeySet.t -> 'a1 -> KeySet.elt
      -> __ -> __ -> 'a1) -> KeySet.t -> 'a1
    
    val set_induction_bis :
      (KeySet.t -> KeySet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (KeySet.elt ->
      KeySet.t -> __ -> 'a1 -> 'a1) -> KeySet.t -> 'a1
    
    val cardinal_inv_2 : KeySet.t -> nat -> KeySet.elt
    
    val cardinal_inv_2b : KeySet.t -> KeySet.elt
   end
  
  module KeySetFacts : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val one : 'a1 -> 'a1 list
  
  val dom : (X.t*'a1) list -> KeySet.t
  
  val get : X.t -> (X.t*'a1) list -> 'a1 option
  
  val map : ('a1 -> 'a2) -> (X.t*'a1) list -> (X.t*'a2) list
  
  val alist_ind :
    'a2 -> (X.t -> 'a1 -> (X.t*'a1) list -> 'a2 -> 'a2) -> (X.t*'a1) list ->
    'a2
  
  val binds_dec :
    X.t -> 'a1 -> (X.t*'a1) list -> ('a1 -> 'a1 -> bool) -> bool
  
  val binds_lookup : X.t -> (X.t*'a1) list -> ('a1, __) sum
 end

