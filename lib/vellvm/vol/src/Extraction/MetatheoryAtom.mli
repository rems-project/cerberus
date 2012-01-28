open CoqFSetDecide
open Datatypes
open EquivDec
open FSetExtra
open FSetFacts
open FSetProperties
open FSetWeakNotin
open MinMax
open Peano_dec

type __ = Obj.t

module type ATOM = 
 sig 
  type atom = String.t
  
  val eq_atom_dec : atom -> atom -> bool
  
  val atom_fresh_for_list : atom list -> atom
 end

module AtomImpl : 
 ATOM

module AtomDT : 
 sig 
  type t = AtomImpl.atom
  
  val eq_dec : AtomImpl.atom -> AtomImpl.atom -> bool
 end

val coq_EqDec_atom : AtomImpl.atom coq_EqDec

val coq_EqDec_nat : nat coq_EqDec

module AtomSetImpl : 
 sig 
  type elt = AtomImpl.atom
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : AtomImpl.atom -> t -> bool
  
  val add : AtomImpl.atom -> t -> t
  
  val singleton : AtomImpl.atom -> t
  
  val remove : AtomImpl.atom -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (AtomImpl.atom -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (AtomImpl.atom -> bool) -> t -> bool
  
  val exists_ : (AtomImpl.atom -> bool) -> t -> bool
  
  val filter : (AtomImpl.atom -> bool) -> t -> t
  
  val partition : (AtomImpl.atom -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> AtomImpl.atom list
  
  val choose : t -> AtomImpl.atom option
 end

module AtomSetDecide : 
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

module AtomSetNotin : 
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
 end

module AtomSetFacts : 
 sig 
  val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
 end

module AtomSetProperties : 
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
    (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t -> (AtomSetImpl.t
    -> __ -> 'a2) -> (AtomSetImpl.elt -> 'a1 -> AtomSetImpl.t ->
    AtomSetImpl.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t -> (AtomSetImpl.t
    -> AtomSetImpl.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (AtomSetImpl.elt
    -> 'a1 -> AtomSetImpl.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t -> 'a2 ->
    (AtomSetImpl.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> (AtomSetImpl.t -> AtomSetImpl.t
    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (AtomSetImpl.elt -> 'a1 ->
    AtomSetImpl.t -> __ -> 'a2 -> 'a2) -> AtomSetImpl.t -> 'a2
  
  val fold_rel :
    (AtomSetImpl.elt -> 'a1 -> 'a1) -> (AtomSetImpl.elt -> 'a2 -> 'a2) -> 'a1
    -> 'a2 -> AtomSetImpl.t -> 'a3 -> (AtomSetImpl.elt -> 'a1 -> 'a2 -> __ ->
    'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (AtomSetImpl.t -> __ -> 'a1) -> (AtomSetImpl.t -> AtomSetImpl.t -> 'a1 ->
    AtomSetImpl.elt -> __ -> __ -> 'a1) -> AtomSetImpl.t -> 'a1
  
  val set_induction_bis :
    (AtomSetImpl.t -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (AtomSetImpl.elt -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> AtomSetImpl.t
    -> 'a1
  
  val cardinal_inv_2 : AtomSetImpl.t -> nat -> AtomSetImpl.elt
  
  val cardinal_inv_2b : AtomSetImpl.t -> AtomSetImpl.elt
 end

val atom_fresh : AtomSetImpl.t -> AtomImpl.atom

