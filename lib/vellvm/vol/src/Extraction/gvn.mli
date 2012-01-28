open Bool
open Coqlib
open Datatypes
open Iteration
open Kildall
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Peano
open Specif
open Analysis
open Dtree
open Infrastructure
open Primitives
open Syntax

val cmds_from_block :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.cmds option

type rhs =
  | Coq_rhs_bop of LLVMsyntax.bop * LLVMsyntax.sz * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_fbop of LLVMsyntax.fbop * LLVMsyntax.floating_point
     * LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_extractvalue of LLVMsyntax.typ * LLVMsyntax.value
     * LLVMsyntax.list_const
  | Coq_rhs_insertvalue of LLVMsyntax.typ * LLVMsyntax.value * 
     LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.list_const
  | Coq_rhs_malloc of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_free of LLVMsyntax.typ * LLVMsyntax.value
  | Coq_rhs_alloca of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_load of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_store of LLVMsyntax.typ * LLVMsyntax.value * 
     LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_gep of LLVMsyntax.inbounds * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.list_sz_value
  | Coq_rhs_trunc of LLVMsyntax.truncop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_ext of LLVMsyntax.extop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_cast of LLVMsyntax.castop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_icmp of LLVMsyntax.cond * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_fcmp of LLVMsyntax.fcond * LLVMsyntax.floating_point
     * LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_select of LLVMsyntax.value * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_call of LLVMsyntax.noret * LLVMsyntax.clattrs * 
     LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.params

val rhs_rect :
  (LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value ->
  'a1) -> (LLVMsyntax.fbop -> LLVMsyntax.floating_point -> LLVMsyntax.value
  -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.list_const -> 'a1) ->
  (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
  (LLVMsyntax.typ -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
  (LLVMsyntax.inbounds -> LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.list_sz_value -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ
  -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) ->
  (LLVMsyntax.castop -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ
  -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.value -> 'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point
  -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.value ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1) ->
  (LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.params -> 'a1) -> rhs -> 'a1

val rhs_rec :
  (LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value ->
  'a1) -> (LLVMsyntax.fbop -> LLVMsyntax.floating_point -> LLVMsyntax.value
  -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.list_const -> 'a1) ->
  (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
  (LLVMsyntax.typ -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
  (LLVMsyntax.inbounds -> LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.list_sz_value -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ
  -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) ->
  (LLVMsyntax.castop -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ
  -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> LLVMsyntax.value ->
  LLVMsyntax.value -> 'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point
  -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.value ->
  LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1) ->
  (LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ ->
  LLVMsyntax.value -> LLVMsyntax.params -> 'a1) -> rhs -> 'a1

val rhs_of_cmd : LLVMsyntax.cmd -> rhs

val rhs_dec : rhs -> rhs -> bool

val pure_cmd : LLVMsyntax.cmd -> bool

val const_list_value :
  LLVMsyntax.list_sz_value -> LLVMsyntax.list_const option

val const_cmd : LLVMsyntax.cmd -> LLVMsyntax.const option

val const_in_list_value_l :
  LLVMsyntax.const -> LLVMsyntax.list_value_l -> bool

val const_phinode : LLVMsyntax.phinode -> LLVMsyntax.const option

type lcmds = (LLVMsyntax.l*LLVMsyntax.cmd) list

val lookup_redundant_exp : lcmds -> rhs -> LLVMsyntax.id option

val mem_effect : LLVMsyntax.cmd -> (LLVMsyntax.value*LLVMsyntax.typ) option

val is_no_alias_id : LLVMsyntax.id -> LLVMsyntax.id -> bool

val is_no_alias :
  LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ ->
  bool

val kill_aliased_loadstores :
  lcmds -> LLVMsyntax.value -> LLVMsyntax.typ -> lcmds

val is_must_alias_id : LLVMsyntax.id -> LLVMsyntax.id -> bool

val is_must_alias :
  LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ ->
  bool

val lookup_redundant_load :
  lcmds -> LLVMsyntax.typ -> LLVMsyntax.value ->
  ((LLVMsyntax.l*LLVMsyntax.id)*LLVMsyntax.value) option

val block_doesnt_kill :
  LLVMsyntax.block -> LLVMsyntax.value -> LLVMsyntax.typ -> bool

val split_cmds : LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmds

val cmds_doesnt_kill :
  LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.typ ->
  bool

module LBooleanInv : 
 sig 
  type t = bool
  
  val beq : t -> t -> bool
  
  val bot : bool
  
  val top : bool
  
  val lub : t -> t -> bool
 end

module AvailableDS : 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

val available_transf :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
  LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.l -> bool -> bool

val available_init_aux :
  LLVMsyntax.blocks -> LLVMsyntax.l -> (LLVMsyntax.l*bool) list ->
  (LLVMsyntax.l*bool) list

val available_init :
  LLVMsyntax.fdef -> LLVMsyntax.l -> (LLVMsyntax.l*bool) list

val available_aux :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
  LLVMsyntax.value -> LLVMsyntax.typ -> bool AMap.t option

val fdef_doesnt_kill :
  LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
  LLVMsyntax.value -> LLVMsyntax.typ -> bool

val fdef_doesnt_kill_aux_func :
  (LLVMsyntax.fdef, (LLVMsyntax.ls ATree.t, (LLVMsyntax.l list,
  (LLVMsyntax.l, (LLVMsyntax.l, (LLVMsyntax.l, (LLVMsyntax.id,
  (LLVMsyntax.value, LLVMsyntax.typ) sigT) sigT) sigT) sigT) sigT) sigT)
  sigT) sigT -> bool

val fdef_doesnt_kill_aux :
  LLVMsyntax.fdef -> LLVMsyntax.ls ATree.t -> LLVMsyntax.l list ->
  LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
  LLVMsyntax.value -> LLVMsyntax.typ -> bool

val kill_loadstores : lcmds -> lcmds

val does_load_elim : unit -> bool

val gvn_cmd :
  ((LLVMsyntax.fdef*bool)*lcmds) -> LLVMsyntax.l -> LLVMsyntax.cmd ->
  (LLVMsyntax.fdef*bool)*lcmds

val gvn_cmds :
  ((LLVMsyntax.fdef*bool)*lcmds) -> LLVMsyntax.l -> nat ->
  (LLVMsyntax.fdef*bool)*lcmds

val gvn_phis :
  LLVMsyntax.fdef -> bool -> LLVMsyntax.phinodes -> LLVMsyntax.fdef*bool

val gvn_fdef_dtree :
  LLVMsyntax.fdef -> bool -> lcmds -> coq_DTree -> LLVMsyntax.fdef*bool

val gvn_fdef_dtrees :
  LLVMsyntax.fdef -> bool -> lcmds -> coq_DTrees -> LLVMsyntax.fdef*bool

val lookup_predundant_exp_from_cmds :
  LLVMsyntax.cmds -> rhs -> LLVMsyntax.cmd option

val lookup_predundant_exp_for_id :
  LLVMsyntax.fdef -> LLVMsyntax.l list -> AtomImpl.atom set -> Dominators.t
  AMap.t -> LLVMsyntax.l -> rhs -> (LLVMsyntax.l*LLVMsyntax.cmd) option

val lookup_predundant_exp :
  LLVMsyntax.fdef -> AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l
  list -> LLVMsyntax.l list ->
  (((LLVMsyntax.l*LLVMsyntax.id)*LLVMsyntax.l)*LLVMsyntax.cmd) option

val find_gcd_dom :
  AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l ->
  LLVMsyntax.l option

val pre_fdef :
  LLVMsyntax.fdef -> AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l
  list -> LLVMsyntax.fdef*bool

val does_pre : unit -> bool

val opt_step :
  coq_DTree -> AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list
  -> LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum

val dce_block : LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.fdef

val dce_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef

val read_aa_from_fun : LLVMsyntax.id -> bool

val opt_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef

val open_aa_db : unit -> bool

val opt : LLVMsyntax.coq_module -> LLVMsyntax.coq_module

