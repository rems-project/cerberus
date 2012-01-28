open AST
open BinInt
open BinPos
open Coqlib
open Datatypes
open Integers
open Memdata
open Memtype
open Values
open Wf_Z

type __ = Obj.t

val update : coq_Z -> 'a1 -> (coq_Z -> 'a1) -> coq_Z -> 'a1

module Mem : 
 sig 
  type mem_ = { mem_contents : (block -> coq_Z -> memval);
                mem_access : (block -> coq_Z -> permission option);
                bounds : (block -> coq_Z*coq_Z); nextblock : 
                block; maxaddress : coq_Z;
                ptr2int : (block -> coq_Z -> coq_Z option);
                int2ptr : (coq_Z -> (block*coq_Z) option) }
  
  val mem__rect :
    ((block -> coq_Z -> memval) -> (block -> coq_Z -> permission option) ->
    (block -> coq_Z*coq_Z) -> block -> coq_Z -> (block -> coq_Z -> coq_Z
    option) -> (coq_Z -> (block*coq_Z) option) -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> mem_ -> 'a1
  
  val mem__rec :
    ((block -> coq_Z -> memval) -> (block -> coq_Z -> permission option) ->
    (block -> coq_Z*coq_Z) -> block -> coq_Z -> (block -> coq_Z -> coq_Z
    option) -> (coq_Z -> (block*coq_Z) option) -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> mem_ -> 'a1
  
  val mem_contents : mem_ -> block -> coq_Z -> memval
  
  val mem_access : mem_ -> block -> coq_Z -> permission option
  
  val bounds : mem_ -> block -> coq_Z*coq_Z
  
  val nextblock : mem_ -> block
  
  val maxaddress : mem_ -> coq_Z
  
  val ptr2int : mem_ -> block -> coq_Z -> coq_Z option
  
  val int2ptr : mem_ -> coq_Z -> (block*coq_Z) option
  
  type mem = mem_
  
  val perm_order_dec : permission -> permission -> bool
  
  val perm_order'_dec : permission option -> permission -> bool
  
  val perm_dec : mem -> block -> coq_Z -> permission -> bool
  
  val range_perm_dec : mem -> block -> coq_Z -> coq_Z -> permission -> bool
  
  val valid_access_dec :
    mem -> memory_chunk -> block -> coq_Z -> permission -> bool
  
  val valid_pointer : mem -> block -> coq_Z -> bool
  
  val empty : mem
  
  val nullptr : block
  
  val update_int2ptr :
    (coq_Z -> (block*coq_Z) option) -> block -> coq_Z -> coq_Z -> nat ->
    coq_Z -> (block*coq_Z) option
  
  val alloc : mem -> coq_Z -> coq_Z -> mem_*block
  
  val clearN :
    (block -> coq_Z -> memval) -> block -> coq_Z -> coq_Z -> block -> coq_Z
    -> memval
  
  val clear_ptr2int :
    (block -> coq_Z -> coq_Z option) -> block -> coq_Z -> coq_Z -> block ->
    coq_Z -> coq_Z option
  
  val clear_int2ptr :
    (coq_Z -> (block*coq_Z) option) -> block -> coq_Z -> coq_Z -> coq_Z ->
    (block*coq_Z) option
  
  val unchecked_free : mem -> block -> coq_Z -> coq_Z -> mem
  
  val free : mem -> block -> coq_Z -> coq_Z -> mem option
  
  val free_list : mem -> ((block*coq_Z)*coq_Z) list -> mem option
  
  val getN : nat -> coq_Z -> (coq_Z -> memval) -> memval list
  
  val load : memory_chunk -> mem -> block -> coq_Z -> coq_val option
  
  val loadv : memory_chunk -> mem -> coq_val -> coq_val option
  
  val loadbytes : mem -> block -> coq_Z -> coq_Z -> memval list option
  
  val setN : memval list -> coq_Z -> (coq_Z -> memval) -> coq_Z -> memval
  
  val store : memory_chunk -> mem -> block -> coq_Z -> coq_val -> mem option
  
  val storev : memory_chunk -> mem -> coq_val -> coq_val -> mem option
  
  val drop_perm : mem -> block -> coq_Z -> coq_Z -> permission -> mem option
  
  val valid_access_store :
    mem -> memory_chunk -> block -> coq_Z -> coq_val -> mem
  
  val range_perm_free : mem -> block -> coq_Z -> coq_Z -> mem
  
  val range_perm_drop_2 : mem -> block -> coq_Z -> coq_Z -> permission -> mem
  
  val mem_inj_rect : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1
  
  val mem_inj_rec : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1
  
  val extends__rect : mem -> mem -> (__ -> __ -> 'a1) -> 'a1
  
  val extends__rec : mem -> mem -> (__ -> __ -> 'a1) -> 'a1
  
  val inject__rect :
    meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> 'a1
  
  val inject__rec :
    meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> 'a1
  
  val flat_inj : block -> meminj
 end

