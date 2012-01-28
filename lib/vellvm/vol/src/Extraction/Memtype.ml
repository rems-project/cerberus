open AST
open BinInt
open Memdata
open Values

type permission =
  | Freeable
  | Writable
  | Readable
  | Nonempty

(** val permission_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> permission -> 'a1 **)

let permission_rect f f0 f1 f2 = function
  | Freeable -> f
  | Writable -> f0
  | Readable -> f1
  | Nonempty -> f2

(** val permission_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> permission -> 'a1 **)

let permission_rec f f0 f1 f2 = function
  | Freeable -> f
  | Writable -> f0
  | Readable -> f1
  | Nonempty -> f2

module type MEM = 
 sig 
  type mem 
  
  val nullptr : block
  
  val empty : mem
  
  val alloc : mem -> coq_Z -> coq_Z -> mem*block
  
  val free : mem -> block -> coq_Z -> coq_Z -> mem option
  
  val load : memory_chunk -> mem -> block -> coq_Z -> coq_val option
  
  val store : memory_chunk -> mem -> block -> coq_Z -> coq_val -> mem option
  
  val loadv : memory_chunk -> mem -> coq_val -> coq_val option
  
  val storev : memory_chunk -> mem -> coq_val -> coq_val -> mem option
  
  val loadbytes : mem -> block -> coq_Z -> coq_Z -> memval list option
  
  val free_list : mem -> ((block*coq_Z)*coq_Z) list -> mem option
  
  val drop_perm : mem -> block -> coq_Z -> coq_Z -> permission -> mem option
  
  val nextblock : mem -> block
  
  val valid_pointer : mem -> block -> coq_Z -> bool
  
  val bounds : mem -> block -> coq_Z*coq_Z
  
  val valid_access_store :
    mem -> memory_chunk -> block -> coq_Z -> coq_val -> mem
  
  val range_perm_free : mem -> block -> coq_Z -> coq_Z -> mem
  
  val range_perm_drop_2 : mem -> block -> coq_Z -> coq_Z -> permission -> mem
  
  val flat_inj : block -> meminj
 end

