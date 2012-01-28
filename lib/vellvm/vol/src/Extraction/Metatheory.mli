open AssocList
open Datatypes
open MetatheoryAtom

type __ = Obj.t

module EnvImpl : 
 sig 
  module D : 
   sig 
    module F : 
     sig 
      val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
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
        val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
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
      val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
     end
    
    val coq_In_dec : AtomSetImpl.elt -> AtomSetImpl.t -> bool
    
    val of_list : AtomSetImpl.elt list -> AtomSetImpl.t
    
    val to_list : AtomSetImpl.t -> AtomSetImpl.elt list
    
    val fold_rec :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t ->
      (AtomSetImpl.t -> __ -> 'a2) -> (AtomSetImpl.elt -> 'a1 ->
      AtomSetImpl.t -> AtomSetImpl.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_bis :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t ->
      (AtomSetImpl.t -> AtomSetImpl.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (AtomSetImpl.elt -> 'a1 -> AtomSetImpl.t -> __ -> __ -> 'a2 -> 'a2) ->
      'a2
    
    val fold_rec_nodep :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t -> 'a2 ->
      (AtomSetImpl.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> (AtomSetImpl.t ->
      AtomSetImpl.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (AtomSetImpl.elt ->
      'a1 -> AtomSetImpl.t -> __ -> 'a2 -> 'a2) -> AtomSetImpl.t -> 'a2
    
    val fold_rel :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> (AtomSetImpl.elt -> 'a2 -> 'a2) ->
      'a1 -> 'a2 -> AtomSetImpl.t -> 'a3 -> (AtomSetImpl.elt -> 'a1 -> 'a2 ->
      __ -> 'a3 -> 'a3) -> 'a3
    
    val set_induction :
      (AtomSetImpl.t -> __ -> 'a1) -> (AtomSetImpl.t -> AtomSetImpl.t -> 'a1
      -> AtomSetImpl.elt -> __ -> __ -> 'a1) -> AtomSetImpl.t -> 'a1
    
    val set_induction_bis :
      (AtomSetImpl.t -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (AtomSetImpl.elt -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> AtomSetImpl.t
      -> 'a1
    
    val cardinal_inv_2 : AtomSetImpl.t -> nat -> AtomSetImpl.elt
    
    val cardinal_inv_2b : AtomSetImpl.t -> AtomSetImpl.elt
   end
  
  module KeySetFacts : 
   sig 
    val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
   end
  
  val one : 'a1 -> 'a1 list
  
  val dom : (AtomImpl.atom*'a1) list -> AtomSetImpl.t
  
  val get : AtomImpl.atom -> (AtomImpl.atom*'a1) list -> 'a1 option
  
  val map :
    ('a1 -> 'a2) -> (AtomImpl.atom*'a1) list -> (AtomImpl.atom*'a2) list
  
  val alist_ind :
    'a2 -> (AtomImpl.atom -> 'a1 -> (AtomImpl.atom*'a1) list -> 'a2 -> 'a2)
    -> (AtomImpl.atom*'a1) list -> 'a2
  
  val binds_dec :
    AtomImpl.atom -> 'a1 -> (AtomImpl.atom*'a1) list -> ('a1 -> 'a1 -> bool)
    -> bool
  
  val binds_lookup :
    AtomImpl.atom -> (AtomImpl.atom*'a1) list -> ('a1, __) sum
 end

