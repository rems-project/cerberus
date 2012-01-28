open Datatypes
open FSetDecide
open FSetInterface
open List0

type __ = Obj.t

module WProperties_fun : 
 functor (E:DecidableType.DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
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
  module Dec : 
   sig 
    module F : 
     sig 
      val eqb : E.t -> E.t -> bool
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
    val eqb : E.t -> E.t -> bool
   end
  
  val coq_In_dec : M.elt -> M.t -> bool
  
  val of_list : M.elt list -> M.t
  
  val to_list : M.t -> M.elt list
  
  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
    'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2
    -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
  
  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
    'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 ->
    'a1) -> M.t -> 'a1
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
 end

module WProperties : 
 functor (M:WS) ->
 sig 
  module Dec : 
   sig 
    module F : 
     sig 
      val eqb : M.E.t -> M.E.t -> bool
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
    val eqb : M.E.t -> M.E.t -> bool
   end
  
  val coq_In_dec : M.elt -> M.t -> bool
  
  val of_list : M.elt list -> M.t
  
  val to_list : M.t -> M.elt list
  
  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
    'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2
    -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
  
  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
    'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 ->
    'a1) -> M.t -> 'a1
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
 end

module Properties : 
 functor (M:WS) ->
 sig 
  module Dec : 
   sig 
    module F : 
     sig 
      val eqb : M.E.t -> M.E.t -> bool
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
    val eqb : M.E.t -> M.E.t -> bool
   end
  
  val coq_In_dec : M.elt -> M.t -> bool
  
  val of_list : M.elt list -> M.t
  
  val to_list : M.t -> M.elt list
  
  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
    'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2
    -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
  
  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
    'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 ->
    'a1) -> M.t -> 'a1
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
 end

module OrdProperties : 
 functor (M:S) ->
 sig 
  module ME : 
   sig 
    module OrderElts : 
     sig 
      type t = M.E.t
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : M.E.t -> M.E.t -> bool
    
    val lt_dec : M.E.t -> M.E.t -> bool
    
    val eqb : M.E.t -> M.E.t -> bool
   end
  
  module P : 
   sig 
    module Dec : 
     sig 
      module F : 
       sig 
        val eqb : M.E.t -> M.E.t -> bool
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
      val eqb : M.E.t -> M.E.t -> bool
     end
    
    val coq_In_dec : M.elt -> M.t -> bool
    
    val of_list : M.elt list -> M.t
    
    val to_list : M.t -> M.elt list
    
    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) ->
      'a2
    
    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
    
    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
    
    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1
    
    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1
    
    val cardinal_inv_2 : M.t -> nat -> M.elt
    
    val cardinal_inv_2b : M.t -> M.elt
   end
  
  val gtb : M.E.t -> M.E.t -> bool
  
  val leb : M.E.t -> M.E.t -> bool
  
  val elements_lt : M.E.t -> M.t -> M.E.t list
  
  val elements_ge : M.E.t -> M.t -> M.E.t list
  
  val set_induction_max :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_min :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1) ->
    M.t -> 'a1
 end

