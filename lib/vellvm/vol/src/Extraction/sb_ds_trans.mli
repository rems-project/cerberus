open BinInt
open BinPos
open Datatypes
open Metatheory
open MetatheoryAtom
open Peano
open Alist
open Infrastructure
open Monad
open Sb_def
open Syntax

module SB_ds_pass : 
 sig 
  val i32 : LLVMsyntax.typ
  
  val i1 : LLVMsyntax.typ
  
  val pp8 : LLVMsyntax.typ
  
  val p32 : LLVMsyntax.typ
  
  val int1 : LLVMsyntax.const
  
  val vint1 : LLVMsyntax.value
  
  val c1 : LLVMsyntax.list_sz_value
  
  val vnullp8 : LLVMsyntax.value
  
  val vnullp32 : LLVMsyntax.value
  
  val int0 : LLVMsyntax.const
  
  val vint0 : LLVMsyntax.value
  
  val assert_fid : LLVMsyntax.id
  
  val fake_id : LLVMsyntax.id
  
  val gmb_fid : LLVMsyntax.id
  
  val gme_fid : LLVMsyntax.id
  
  val smmd_fid : LLVMsyntax.id
  
  val ssb_fid : LLVMsyntax.id
  
  val sse_fid : LLVMsyntax.id
  
  val gsb_fid : LLVMsyntax.id
  
  val gse_fid : LLVMsyntax.id
  
  val astk_fid : LLVMsyntax.id
  
  val dstk_fid : LLVMsyntax.id
  
  val assert_typ : LLVMsyntax.typ
  
  val assert_fn : LLVMsyntax.value
  
  val gmb_typ : LLVMsyntax.typ
  
  val gmb_fn : LLVMsyntax.value
  
  val gme_typ : LLVMsyntax.typ
  
  val gme_fn : LLVMsyntax.value
  
  val smmd_typ : LLVMsyntax.typ
  
  val smmd_fn : LLVMsyntax.value
  
  val ssb_typ : LLVMsyntax.typ
  
  val ssb_fn : LLVMsyntax.value
  
  val sse_typ : LLVMsyntax.typ
  
  val sse_fn : LLVMsyntax.value
  
  val gsb_typ : LLVMsyntax.typ
  
  val gsb_fn : LLVMsyntax.value
  
  val gse_typ : LLVMsyntax.typ
  
  val gse_fn : LLVMsyntax.value
  
  val astk_typ : LLVMsyntax.typ
  
  val astk_fn : LLVMsyntax.value
  
  val dstk_typ : LLVMsyntax.typ
  
  val dstk_fn : LLVMsyntax.value
  
  val attrs : LLVMsyntax.clattrs
  
  val getGEPTyp :
    LLVMsyntax.namedts -> LLVMsyntax.list_sz_value -> LLVMsyntax.typ ->
    LLVMsyntax.typ option
  
  val getCmdTyp :
    LLVMsyntax.namedts -> LLVMsyntax.cmd -> LLVMsyntax.typ option
  
  type rmap = (LLVMsyntax.id*(LLVMsyntax.id*LLVMsyntax.id)) list
  
  val getFdefLocs : LLVMsyntax.fdef -> LLVMsyntax.ids
  
  val gen_metadata_id :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.id ->
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.ids)*rmap
  
  val gen_metadata_cmds :
    LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.cmds ->
    (LLVMsyntax.ids*rmap) option
  
  val gen_metadata_phinodes :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.phinodes -> LLVMsyntax.ids*rmap
  
  val gen_metadata_block :
    LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.block ->
    (LLVMsyntax.ids*rmap) option
  
  val gen_metadata_blocks :
    LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.blocks ->
    (LLVMsyntax.ids*rmap) option
  
  val gen_metadata_args :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.args -> LLVMsyntax.ids*rmap
  
  val gen_metadata_fdef :
    LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.fdef ->
    (LLVMsyntax.ids*rmap) option
  
  val isSysLib : LLVMsyntax.id -> bool
  
  val wrapper_fid : LLVMsyntax.id -> LLVMsyntax.id
  
  val isCallLib : LLVMsyntax.id -> bool
  
  val mk_tmp : LLVMsyntax.ids -> LLVMsyntax.id*LLVMsyntax.ids
  
  val type_size : LLVMsyntax.typ -> LLVMsyntax.value
  
  val get_reg_metadata :
    rmap -> LLVMsyntax.value -> (LLVMsyntax.value*LLVMsyntax.value) option
  
  val prop_metadata :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd -> LLVMsyntax.value ->
    AtomImpl.atom -> (LLVMsyntax.ids*LLVMsyntax.cmd list) option
  
  val val32 :
    coq_Z -> (LLVMsyntax.typ*LLVMsyntax.attribute list)*LLVMsyntax.value
  
  val call_set_shadowstack :
    LLVMsyntax.value -> LLVMsyntax.value -> coq_Z -> LLVMsyntax.cmd list ->
    LLVMsyntax.cmds
  
  val trans_params :
    rmap -> LLVMsyntax.params -> coq_Z -> LLVMsyntax.cmds option
  
  val wrap_call : LLVMsyntax.value -> LLVMsyntax.value
  
  val isReturnPointerTypB : LLVMsyntax.typ -> bool
  
  val call_suffix :
    AtomImpl.atom -> bool -> LLVMsyntax.clattrs -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.params -> (LLVMsyntax.id*LLVMsyntax.id)
    coq_AssocList -> LLVMsyntax.cmds option
  
  val trans_cmd :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd ->
    (LLVMsyntax.ids*LLVMsyntax.cmds) option
  
  val trans_cmds :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd list ->
    (LLVMsyntax.ids*LLVMsyntax.cmds) option
  
  val get_metadata_from_list_value_l :
    rmap -> LLVMsyntax.list_value_l ->
    (LLVMsyntax.list_value_l*LLVMsyntax.list_value_l) option
  
  val trans_phinodes :
    rmap -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes option
  
  val trans_terminator :
    rmap -> LLVMsyntax.terminator -> LLVMsyntax.cmds option
  
  val trans_block :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.block ->
    (LLVMsyntax.ids*LLVMsyntax.block) option
  
  val trans_blocks :
    LLVMsyntax.ids -> rmap -> LLVMsyntax.blocks ->
    (LLVMsyntax.ids*LLVMsyntax.blocks) option
  
  val call_get_shadowstack :
    LLVMsyntax.id -> LLVMsyntax.id -> coq_Z -> LLVMsyntax.cmd list ->
    LLVMsyntax.cmds
  
  val trans_args : rmap -> LLVMsyntax.args -> coq_Z -> LLVMsyntax.cmds option
  
  val trans_fdef :
    LLVMsyntax.namedts -> LLVMsyntax.fdef -> LLVMsyntax.fdef option
  
  val trans_fdec : LLVMsyntax.fdec -> LLVMsyntax.fdec
  
  val trans_product :
    LLVMsyntax.namedts -> LLVMsyntax.product -> LLVMsyntax.product option
  
  val trans_products :
    LLVMsyntax.namedts -> LLVMsyntax.products -> LLVMsyntax.products option
  
  val trans_module : LLVMsyntax.coq_module -> LLVMsyntax.coq_module option
  
  val trans_system : LLVMsyntax.system -> LLVMsyntax.system option
  
  val getValueID : LLVMsyntax.value -> AtomSetImpl.t
  
  val ids2atoms : LLVMsyntax.ids -> AtomSetImpl.t
  
  val codom : rmap -> AtomSetImpl.t
 end

