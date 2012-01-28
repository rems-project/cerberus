open Coqlib
open Datatypes
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Specif
open Analysis
open Infrastructure
open Syntax

val reachablity_analysis_aux_func :
  (LLVMsyntax.l list, (LLVMsyntax.ls ATree.t, (LLVMsyntax.l, LLVMsyntax.l
  list) sigT) sigT) sigT -> LLVMsyntax.l list option

val reachablity_analysis_aux :
  LLVMsyntax.l list -> LLVMsyntax.ls ATree.t -> LLVMsyntax.l -> LLVMsyntax.l
  list -> LLVMsyntax.l list option

val get_reachable_labels :
  LLVMsyntax.l list -> bool AMap.t -> LLVMsyntax.l list -> LLVMsyntax.l list

val reachablity_analysis : LLVMsyntax.fdef -> LLVMsyntax.l list option

type coq_DTree =
  | DT_node of LLVMsyntax.l * coq_DTrees
and coq_DTrees =
  | DT_nil
  | DT_cons of coq_DTree * coq_DTrees

val coq_DTree_rect : (LLVMsyntax.l -> coq_DTrees -> 'a1) -> coq_DTree -> 'a1

val coq_DTree_rec : (LLVMsyntax.l -> coq_DTrees -> 'a1) -> coq_DTree -> 'a1

val coq_DTrees_rect :
  'a1 -> (coq_DTree -> coq_DTrees -> 'a1 -> 'a1) -> coq_DTrees -> 'a1

val coq_DTrees_rec :
  'a1 -> (coq_DTree -> coq_DTrees -> 'a1 -> 'a1) -> coq_DTrees -> 'a1

val dtree_dom : coq_DTree -> AtomSetImpl.t

val dtrees_dom : coq_DTrees -> AtomSetImpl.t

val get_dtree_root : coq_DTree -> LLVMsyntax.l

val gt_sdom :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l ->
  bool

val find_min :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
  set -> LLVMsyntax.l

val insert_sort_sdom_iter :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
  list -> LLVMsyntax.l list -> LLVMsyntax.l list

val insert_sort_sdom :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
  LLVMsyntax.l list -> LLVMsyntax.l list

val sort_sdom :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
  LLVMsyntax.l list

val getEntryLabel : LLVMsyntax.fdef -> LLVMsyntax.l option

val remove_redundant : LLVMsyntax.l list -> LLVMsyntax.l list

val compute_sdom_chains_aux :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
  (LLVMsyntax.l*LLVMsyntax.l list) list -> (LLVMsyntax.l*LLVMsyntax.l list)
  list

val compute_sdom_chains :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
  (LLVMsyntax.l*LLVMsyntax.l list) list

val in_children_roots : LLVMsyntax.l -> coq_DTrees -> bool

val dtree_insert : coq_DTree -> LLVMsyntax.id -> LLVMsyntax.l -> coq_DTree

val dtrees_insert : coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.l -> coq_DTrees

val is_dtree_edge : coq_DTree -> LLVMsyntax.id -> LLVMsyntax.l -> bool

val is_dtrees_edge : coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.l -> bool

val dtrees_rec2 :
  (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
  coq_DTrees -> 'a2 -> 'a2) -> coq_DTrees -> 'a2

val dtree_rec2 :
  (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
  coq_DTrees -> 'a2 -> 'a2) -> coq_DTree -> 'a1

val dtree_mutrec :
  (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
  coq_DTrees -> 'a2 -> 'a2) -> (coq_DTree -> 'a1)*(coq_DTrees -> 'a2)

val create_dtree_from_chain : coq_DTree -> LLVMsyntax.id list -> coq_DTree

val create_dtree : LLVMsyntax.fdef -> coq_DTree option

val size_of_dtrees : coq_DTrees -> nat

val find_idom_aux :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
  set -> LLVMsyntax.l option

val find_idom :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
  option

val compute_idoms :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
  (LLVMsyntax.l*LLVMsyntax.l) list -> (LLVMsyntax.l*LLVMsyntax.l) list

