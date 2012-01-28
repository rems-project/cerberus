open Coqlib
open Datatypes
open EqNat
open Iteration
open Kildall
open List0
open Maps
open Metatheory
open MetatheoryAtom
open Alist
open Analysis
open Dtree
open Infrastructure
open Primitives
open Syntax

type vmap = { alloca : LLVMsyntax.value;
              others : LLVMsyntax.value coq_AssocList }

val vmap_rect :
  (LLVMsyntax.value -> LLVMsyntax.value coq_AssocList -> 'a1) -> vmap -> 'a1

val vmap_rec :
  (LLVMsyntax.value -> LLVMsyntax.value coq_AssocList -> 'a1) -> vmap -> 'a1

val alloca : vmap -> LLVMsyntax.value

val others : vmap -> LLVMsyntax.value coq_AssocList

val vm_subst_cmd : vmap -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val vm_subst_tmn : vmap -> LLVMsyntax.terminator -> LLVMsyntax.terminator

val vm_subst_phi : vmap -> LLVMsyntax.phinode -> LLVMsyntax.phinode

val vm_get_alloca : vmap -> LLVMsyntax.value

val vm_set_others : vmap -> AtomImpl.atom -> LLVMsyntax.value -> vmap

val vm_set_alloca : vmap -> LLVMsyntax.value -> vmap

val ssa_renaming_cmd :
  LLVMsyntax.cmd -> LLVMsyntax.id -> vmap -> LLVMsyntax.cmd option*vmap

val ssa_renaming_cmds :
  LLVMsyntax.cmds -> LLVMsyntax.id -> vmap -> LLVMsyntax.cmds*vmap

val vm_subst_value : vmap -> LLVMsyntax.value -> LLVMsyntax.value

val ssa_renaming_phis_operands :
  LLVMsyntax.l -> LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id list
  -> vmap -> LLVMsyntax.phinodes

val block_subst :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.fdef

val ssa_renaming_succ_phis :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l list -> LLVMsyntax.id ->
  LLVMsyntax.id list -> vmap -> LLVMsyntax.fdef

val update_vm_by_phis :
  LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id list -> vmap -> vmap

val ssa_renaming_dtree :
  LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.id -> LLVMsyntax.id list -> vmap
  -> LLVMsyntax.fdef

val ssa_renaming_dtrees :
  LLVMsyntax.fdef -> coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.id list ->
  vmap -> LLVMsyntax.fdef

val vm_init : LLVMsyntax.typ -> vmap

val ssa_renaming :
  LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.id -> LLVMsyntax.typ ->
  LLVMsyntax.id list -> LLVMsyntax.fdef

val insert_phis :
  LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.id -> LLVMsyntax.typ ->
  LLVMsyntax.fdef*LLVMsyntax.id list

val is_promotable : LLVMsyntax.fdef -> LLVMsyntax.id -> bool

val find_promotable_alloca :
  LLVMsyntax.fdef -> LLVMsyntax.cmds -> LLVMsyntax.id list ->
  ((LLVMsyntax.id*LLVMsyntax.typ)*LLVMsyntax.align) option

val mem2reg_fdef_iter :
  LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.l list -> LLVMsyntax.id list ->
  (LLVMsyntax.fdef*bool)*LLVMsyntax.id list

val gen_fresh_ids :
  LLVMsyntax.id list -> AtomImpl.atom list ->
  ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t*AtomImpl.atom list

val gen_phinode :
  LLVMsyntax.id -> LLVMsyntax.typ ->
  ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l list
  -> LLVMsyntax.phinode

val phinodes_placement_block :
  LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.align ->
  ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l list
  ATree.t -> LLVMsyntax.l list ATree.t -> LLVMsyntax.block ->
  LLVMsyntax.block

val phinodes_placement_blocks :
  LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.align ->
  ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l list
  ATree.t -> LLVMsyntax.l list ATree.t -> LLVMsyntax.blocks

val phinodes_placement :
  LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.id -> LLVMsyntax.typ ->
  LLVMsyntax.align -> LLVMsyntax.l list ATree.t -> LLVMsyntax.l list ATree.t
  -> LLVMsyntax.fdef

val find_init_stld :
  LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id list ->
  ((LLVMsyntax.id*LLVMsyntax.value)*LLVMsyntax.cmds,
  LLVMsyntax.value*LLVMsyntax.cmds) sum option

val find_next_stld :
  LLVMsyntax.cmds -> LLVMsyntax.id -> (LLVMsyntax.id,
  LLVMsyntax.id*LLVMsyntax.value) sum option

val elim_stld_cmds :
  LLVMsyntax.fdef -> LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id list
  -> (LLVMsyntax.fdef*bool)*LLVMsyntax.id list

val elim_stld_blocks :
  LLVMsyntax.fdef -> LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.id list
  -> (LLVMsyntax.fdef*bool)*LLVMsyntax.id list

val elim_stld_fdef :
  LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.id list ->
  (LLVMsyntax.fdef*bool)*LLVMsyntax.id list

val elim_stld_step :
  LLVMsyntax.id -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
  (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
  sum

val does_stld_elim : unit -> bool

val load_in_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> bool

val load_in_block : LLVMsyntax.id -> LLVMsyntax.block -> bool

val load_in_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> bool

val elim_dead_st_cmds : LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmds

val elim_dead_st_block :
  LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block

val elim_dead_st_fdef : LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.fdef

val macro_mem2reg_fdef_iter :
  LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.l list ATree.t ->
  LLVMsyntax.l list ATree.t -> LLVMsyntax.id list ->
  (LLVMsyntax.fdef*bool)*LLVMsyntax.id list

val macro_mem2reg_fdef_step :
  LLVMsyntax.l list -> LLVMsyntax.l list ATree.t -> LLVMsyntax.l list ATree.t
  -> (LLVMsyntax.fdef*LLVMsyntax.id list) -> (LLVMsyntax.fdef*LLVMsyntax.id
  list, LLVMsyntax.fdef*LLVMsyntax.id list) sum

val mem2reg_fdef_step :
  coq_DTree -> LLVMsyntax.l list -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
  (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
  sum

val remove_redundancy : LLVMsyntax.ids -> LLVMsyntax.ids -> LLVMsyntax.ids

val eliminate_phi :
  LLVMsyntax.fdef -> LLVMsyntax.phinode -> LLVMsyntax.fdef*bool

val eliminate_phis :
  LLVMsyntax.fdef -> LLVMsyntax.phinodes -> LLVMsyntax.fdef*bool

val eliminate_blocks :
  LLVMsyntax.fdef -> LLVMsyntax.blocks -> LLVMsyntax.fdef*bool

val eliminate_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef*bool

val eliminate_step :
  LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum

val does_phi_elim : unit -> bool

val does_macro_m2r : unit -> bool

val mem2reg_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef

val run : LLVMsyntax.coq_module -> LLVMsyntax.coq_module

