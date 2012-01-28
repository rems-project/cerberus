open Coqlib
open Datatypes
open Iteration
open Lattice
open ListSet
open Maps
open MetatheoryAtom

type __ = Obj.t

val successors_list :
  AtomImpl.atom list ATree.t -> AtomImpl.atom -> AtomImpl.atom list

module type DATAFLOW_SOLVER = 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

module type NODE_SET = 
 sig 
  type t 
  
  val add : AtomImpl.atom -> t -> t
  
  val pick : t -> (AtomImpl.atom*t) option
  
  val initial : AtomImpl.atom list ATree.t -> t
 end

module Dataflow_Solver : 
 functor (LAT:SEMILATTICE) ->
 functor (NS:NODE_SET) ->
 DATAFLOW_SOLVER with module L = LAT

val add_successors :
  AtomImpl.atom list ATree.t -> AtomImpl.atom -> AtomImpl.atom list ->
  AtomImpl.atom list ATree.t

val make_predecessors :
  AtomImpl.atom list ATree.t -> AtomImpl.atom list ATree.t

module type BACKWARD_DATAFLOW_SOLVER = 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

module Backward_Dataflow_Solver : 
 functor (LAT:SEMILATTICE) ->
 functor (NS:NODE_SET) ->
 BACKWARD_DATAFLOW_SOLVER with module L = LAT

module type ORDERED_TYPE_WITH_TOP = 
 sig 
  type t 
  
  val top : t
 end

module type BBLOCK_SOLVER = 
 sig 
  module L : 
   ORDERED_TYPE_WITH_TOP
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    AtomImpl.atom -> L.t AMap.t option
 end

module BBlock_solver : 
 functor (LAT:ORDERED_TYPE_WITH_TOP) ->
 BBLOCK_SOLVER with module L = LAT

module AtomNodeSet : 
 sig 
  type t = AtomImpl.atom set
  
  val add : AtomImpl.atom -> t -> t
  
  val pick : t -> (AtomImpl.atom*AtomImpl.atom set) option
  
  val initial : AtomImpl.atom list ATree.t -> t
 end

module Dataflow_Solver_Var_Top : 
 functor (NS:NODE_SET) ->
 sig 
  module L : 
   sig 
    type coq_BoundedSet =
      AtomImpl.atom set
      (* singleton inductive, whose constructor was mkBoundedSet *)
    
    val coq_BoundedSet_rect :
      AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
      -> 'a1
    
    val coq_BoundedSet_rec :
      AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
      -> 'a1
    
    val bs_contents :
      AtomImpl.atom set -> coq_BoundedSet -> AtomImpl.atom set
    
    type t = coq_BoundedSet
    
    val eq_dec : AtomImpl.atom set -> t -> t -> bool
    
    val beq : AtomImpl.atom set -> t -> t -> bool
    
    val top : AtomImpl.atom set -> t
    
    val bot : AtomImpl.atom set -> t
    
    val lub : AtomImpl.atom set -> t -> t -> t
    
    val add : AtomImpl.atom set -> t -> AtomImpl.atom -> t
    
    val lubs : AtomImpl.atom set -> t list -> t
   end
  
  type dt = L.t
  
  type state = { st_in : dt AMap.t; st_wrk : NS.t }
  
  val state_rect :
    AtomImpl.atom set -> (dt AMap.t -> NS.t -> 'a1) -> state -> 'a1
  
  val state_rec :
    AtomImpl.atom set -> (dt AMap.t -> NS.t -> 'a1) -> state -> 'a1
  
  val st_in : AtomImpl.atom set -> state -> dt AMap.t
  
  val st_wrk : AtomImpl.atom set -> state -> NS.t
  
  val start_state_in :
    AtomImpl.atom set -> (AtomImpl.atom*dt) list -> dt AMap.t
  
  val start_state :
    AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom*dt)
    list -> state
  
  val propagate_succ :
    AtomImpl.atom set -> state -> dt -> AtomImpl.atom -> state
  
  val propagate_succ_list :
    AtomImpl.atom set -> state -> dt -> AtomImpl.atom set -> state
  
  val step :
    AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom -> dt
    -> dt) -> state -> (dt AMap.t, state) sum
  
  val fixpoint :
    AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom -> dt
    -> dt) -> (AtomImpl.atom*dt) list -> dt AMap.t option
  
  type dt1 = L.t
  
  type dt2 = L.t
 end

