open Coqlib
open Datatypes
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Dtree
open Infrastructure
open Syntax

val subst_value :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.value

val subst_list_value :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.list_sz_value ->
  LLVMsyntax.list_sz_value

val subst_cmd :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val subst_tmn :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.terminator ->
  LLVMsyntax.terminator

val subst_list_value_l :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.list_value_l ->
  LLVMsyntax.list_value_l

val subst_phi :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.phinode ->
  LLVMsyntax.phinode

val subst_insn :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.insn -> LLVMsyntax.insn

val subst_block :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.block -> LLVMsyntax.block

val subst_fdef :
  LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val csubst_fdef :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val csubst_block :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.block -> LLVMsyntax.block

val csubst_phi :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.phinode ->
  LLVMsyntax.phinode

val csubst_cmd :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val csubst_tmn :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.terminator ->
  LLVMsyntax.terminator

val csubst_insn :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.insn -> LLVMsyntax.insn

val csubst_value :
  LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.value -> LLVMsyntax.value

val isubst_fdef :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val isubst_block :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block

val isubst_phi :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.phinode

val isubst_cmd :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val isubst_tmn :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.terminator ->
  LLVMsyntax.terminator

val isubst_insn :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.insn -> LLVMsyntax.insn

val isubst_value :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value

val remove_phinodes :
  LLVMsyntax.id -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes

val remove_cmds : LLVMsyntax.id -> LLVMsyntax.cmds -> LLVMsyntax.cmds

val remove_block : LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block

val remove_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val used_in_value : LLVMsyntax.id -> LLVMsyntax.value -> bool

val used_in_list_value : LLVMsyntax.id -> LLVMsyntax.list_sz_value -> bool

val used_in_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> bool

val used_in_tmn : LLVMsyntax.id -> LLVMsyntax.terminator -> bool

val used_in_list_value_l : LLVMsyntax.id -> LLVMsyntax.list_value_l -> bool

val used_in_phi : LLVMsyntax.id -> LLVMsyntax.phinode -> bool

val used_in_insn : LLVMsyntax.id -> LLVMsyntax.insn -> bool

val used_in_block : LLVMsyntax.id -> LLVMsyntax.block -> bool

val used_in_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> bool

val insert_cmds : nat -> LLVMsyntax.cmd -> LLVMsyntax.cmds -> LLVMsyntax.cmds

val insert_block :
  LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.block ->
  LLVMsyntax.block

val insert_fdef :
  LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val rename_id :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id

val rename_value :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value

val rename_list_value :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.list_sz_value ->
  LLVMsyntax.list_sz_value

val rename_cmd :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val rename_tmn :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.terminator ->
  LLVMsyntax.terminator

val rename_list_value_l :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.list_value_l ->
  LLVMsyntax.list_value_l

val rename_phi :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.phinode

val rename_insn :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.insn -> LLVMsyntax.insn

val rename_block :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block

val rename_fheader :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fheader -> LLVMsyntax.fheader

val rename_fdef :
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val gen_fresh_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd

val motion_block :
  LLVMsyntax.l -> nat -> LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.block
  -> LLVMsyntax.block

val motion_fdef :
  LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val print_reachablity : LLVMsyntax.l list -> bool

val print_dominators : AtomImpl.atom set -> Dominators.t AMap.t -> bool

val print_dtree : coq_DTree -> bool

type coq_TNAME = int

val init_expected_name : unit -> coq_TNAME

val check_bname :
  LLVMsyntax.l -> coq_TNAME -> (LLVMsyntax.l*coq_TNAME) option

val check_vname :
  LLVMsyntax.id -> coq_TNAME -> (LLVMsyntax.id*coq_TNAME) option

val renamel_list_value_l :
  LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.list_value_l ->
  LLVMsyntax.list_value_l

val renamel_phi :
  LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.phinode -> LLVMsyntax.phinode

val renamel_block :
  LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.block

val renamel_fdef :
  LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.fdef -> LLVMsyntax.fdef

val fix_temporary_block :
  LLVMsyntax.fdef -> LLVMsyntax.block -> coq_TNAME ->
  (LLVMsyntax.fdef*coq_TNAME) option

val fix_temporary_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef option

val getFdefLocs : LLVMsyntax.fdef -> LLVMsyntax.ids

