open Datatypes
open Kildall
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Specif
open Infrastructure
open Syntax

type __ = Obj.t

val successors_blocks : LLVMsyntax.blocks -> LLVMsyntax.ls ATree.t

val successors : LLVMsyntax.fdef -> LLVMsyntax.ls ATree.t

val transfer :
  AtomImpl.atom set -> LLVMsyntax.l -> Dominators.t -> Dominators.t

val bound_blocks : LLVMsyntax.blocks -> AtomImpl.atom set

val bound_fdef : LLVMsyntax.fdef -> AtomImpl.atom set

val entry_dom :
  LLVMsyntax.block list -> ((LLVMsyntax.l*Dominators.coq_BoundedSet) option,
  __) sigT

module DomDS : 
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
  
  type state = { st_in : dt AMap.t; st_wrk : AtomNodeSet.t }
  
  val state_rect :
    AtomImpl.atom set -> (dt AMap.t -> AtomNodeSet.t -> 'a1) -> state -> 'a1
  
  val state_rec :
    AtomImpl.atom set -> (dt AMap.t -> AtomNodeSet.t -> 'a1) -> state -> 'a1
  
  val st_in : AtomImpl.atom set -> state -> dt AMap.t
  
  val st_wrk : AtomImpl.atom set -> state -> AtomNodeSet.t
  
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

val dom_analyze : LLVMsyntax.fdef -> Dominators.t AMap.t

module ReachDS : 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

val areachable_aux : LLVMsyntax.fdef -> bool AMap.t option

val areachable : LLVMsyntax.fdef -> bool AMap.t

module EntryDomsOthers : 
 sig 
  val bound : LLVMsyntax.blocks -> AtomImpl.atom set
  
  val predecessors : LLVMsyntax.blocks -> AtomImpl.atom list ATree.t
  
  val transf :
    LLVMsyntax.blocks -> LLVMsyntax.l -> Dominators.t -> Dominators.t
  
  val top : LLVMsyntax.blocks -> Dominators.t
  
  val bot : LLVMsyntax.blocks -> Dominators.t
  
  type dt = DomDS.dt
  
  val lub_of_preds : LLVMsyntax.blocks -> dt AMap.t -> AtomImpl.atom -> dt
 end

val cmds_dominates_cmd :
  LLVMsyntax.cmds -> LLVMsyntax.id -> AtomImpl.atom list

val inscope_of_block :
  LLVMsyntax.fdef -> LLVMsyntax.l -> AtomImpl.atom list option ->
  LLVMsyntax.l -> AtomImpl.atom list option

val inscope_of_id :
  LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.id -> AtomImpl.atom list
  option

val inscope_of_cmd :
  LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.cmd -> AtomImpl.atom list
  option

val inscope_of_tmn :
  LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.terminator ->
  AtomImpl.atom list option

val defs_dominate :
  LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.block -> LLVMsyntax.insn
  -> AtomImpl.atom list option

