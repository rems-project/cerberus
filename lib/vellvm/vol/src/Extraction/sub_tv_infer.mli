open Bool
open CoqEqDec
open Datatypes
open EqNat
open List0
open Metatheory
open MetatheoryAtom
open Peano
open Alist
open Infrastructure
open Sub_symexe
open Sub_tv_def
open Syntax

val is_hashLoadBaseBound : LLVMsyntax.id -> bool

val is_loadStoreDereferenceCheck : LLVMsyntax.id -> bool

val is_callDereferenceCheck : LLVMsyntax.id -> bool

val is_hashStoreBaseBound : LLVMsyntax.id -> bool

val remove_cast_const : LLVMsyntax.const -> LLVMsyntax.const

val remove_cast : SBSE.sterm -> SBSE.sterm

val get_ptr_object_const : LLVMsyntax.const -> LLVMsyntax.const

val get_ptr_object : SBSE.sterm -> SBSE.sterm

val eq_sterm_upto_cast : SBSE.sterm -> SBSE.sterm -> bool

val l_of_arg : unit -> LLVMsyntax.l

type beps = (((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id)*bool) list

type nbeps = (nat*beps) list

type lnbeps = (LLVMsyntax.l*nbeps) list

type flnbeps = (LLVMsyntax.id*lnbeps) list

val add_bep :
  beps -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool -> beps

val add_beps : beps -> beps -> beps

val updateAdd_nbeps : nbeps -> nat -> beps -> nbeps

val update_nbeps : nbeps -> nat -> beps -> nbeps

val lookup_nbeps : nbeps -> nat -> beps option

val metadata_from_bep_aux :
  SBSE.sterm -> SBSE.sterm -> SBSE.sterm -> bool -> beps -> beps

val metadata_from_bep :
  SBSE.sterm -> SBSE.sterm -> SBSE.sterm -> bool -> beps -> beps

val metadata_from_smem : SBSE.smem -> beps -> beps

val metadata_from_sterms_aux : SBSE.smap -> beps -> beps -> beps

val metadata_from_sterms : SBSE.smap -> beps -> beps

val metadata_from_cmds : SBSE.nbranch list -> beps -> beps

val lookupSarg :
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id) list ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
  -> SBSE.sterm option

val metadata_from_params :
  beps -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id) list ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> beps -> beps

val get_arg_metadata : flnbeps -> AtomImpl.atom -> beps

type sicall =
  | Coq_stmn_icall_nptr of LLVMsyntax.id * LLVMsyntax.noret
     * LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  | Coq_stmn_icall_ptr of LLVMsyntax.id * LLVMsyntax.noret
     * LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
     * LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
     LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
     LLVMsyntax.id * LLVMsyntax.const * LLVMsyntax.const * 
     LLVMsyntax.const

val sicall_rect :
  (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ
  -> SBSE.sterm -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  -> 'a1) -> (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
  LLVMsyntax.typ -> SBSE.sterm ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
  -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
  LLVMsyntax.const -> 'a1) -> sicall -> 'a1

val sicall_rec :
  (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ
  -> SBSE.sterm -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  -> 'a1) -> (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
  LLVMsyntax.typ -> SBSE.sterm ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
  -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
  LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
  LLVMsyntax.const -> 'a1) -> sicall -> 'a1

val se_icall : SBSE.sstate -> SBsyntax.call -> sicall

val metadata_from_iscall :
  SBsyntax.products -> flnbeps -> beps -> sicall -> beps

val metadata_from_subblock :
  SBsyntax.products -> flnbeps -> SBsyntax.subblock -> beps -> beps

val metadata_diff_cmds : beps -> LLVMsyntax.cmds -> beps

val update_pred_subblock : nbeps -> nat -> beps -> nbeps

val metadata_from_subblocks_aux :
  SBsyntax.products -> flnbeps -> nat -> SBsyntax.subblock list -> nbeps ->
  nbeps

val metadata_from_subblocks :
  SBsyntax.products -> flnbeps -> SBsyntax.subblock list -> nbeps -> nbeps

val lookupPhinode :
  LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.phinode option

val update_block_metadata : lnbeps -> LLVMsyntax.l -> beps -> lnbeps

val metadata_from_value :
  LLVMsyntax.l -> LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.value ->
  bool -> lnbeps -> lnbeps

val metadata_from_list_value_l :
  LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l ->
  LLVMsyntax.list_value_l -> bool -> lnbeps -> lnbeps

val metadata_from_phinodes : LLVMsyntax.phinodes -> lnbeps -> beps -> lnbeps

val updatePredBlocks : LLVMsyntax.l list -> lnbeps -> beps -> lnbeps

val metadata_diff_phinodes : beps -> LLVMsyntax.phinodes -> beps

type usedef_block = (LLVMsyntax.l*LLVMsyntax.l list) list

val update_udb : usedef_block -> LLVMsyntax.l -> LLVMsyntax.l -> usedef_block

val genBlockUseDef_block : SBsyntax.block -> usedef_block -> usedef_block

val genBlockUseDef_blocks :
  SBsyntax.block list -> usedef_block -> usedef_block

val genBlockUseDef_fdef : SBsyntax.fdef -> usedef_block

val metadata_from_block_aux :
  SBsyntax.products -> flnbeps -> (nat*beps) list coq_AssocList ->
  AtomImpl.atom -> LLVMsyntax.phinodes -> SBsyntax.subblock list ->
  SBSE.nbranch list -> LLVMsyntax.l list coq_AssocList -> lnbeps

val metadata_from_block :
  SBsyntax.products -> flnbeps -> SBsyntax.block -> usedef_block -> lnbeps ->
  lnbeps

val metadata_from_blocks_aux :
  SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
  -> lnbeps

val eq_nbeps : nbeps -> nbeps -> bool

val eq_lnbeps : lnbeps -> lnbeps -> bool

val onat_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

val onat_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

val metadata_from_blocks :
  SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
  -> int -> lnbeps

val metadata_from_args : LLVMsyntax.args -> beps -> beps -> beps

val metadata_from_fdef :
  SBsyntax.products -> flnbeps -> SBsyntax.fdef -> lnbeps -> int -> lnbeps

val metadata_from_products_aux :
  SBsyntax.products -> SBsyntax.products -> flnbeps -> int -> flnbeps

val eq_flnbeps : flnbeps -> flnbeps -> bool

val metadata_from_products :
  SBsyntax.products -> flnbeps -> int -> int -> flnbeps

val metadata_from_module : SBsyntax.coq_module -> int -> int -> flnbeps

val validate_metadata_from_blocks :
  SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
  -> bool

val nbeps_to_beps : nbeps -> beps -> beps

val lnbeps_to_nbeps : lnbeps -> nbeps -> nbeps

val in_beps :
  beps -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool -> bool

val disjoint_mptr_fptr_metadata_aux : beps -> bool

val disjoint_mptr_fptr_metadata : lnbeps -> bool

val validate_metadata_from_fdef :
  SBsyntax.products -> flnbeps -> SBsyntax.fdef -> lnbeps -> bool

val validate_metadata_from_products_aux :
  SBsyntax.products -> SBsyntax.products -> flnbeps -> bool

val validate_metadata_from_module : SBsyntax.coq_module -> flnbeps -> bool

type abes = (LLVMsyntax.id*LLVMsyntax.id) list

val add_abes : abes -> LLVMsyntax.id -> LLVMsyntax.id -> abes

val addrofbe_from_smem : SBSE.smem -> abes -> abes

val addrofbe_from_cmds : SBSE.nbranch list -> abes -> abes

val addrofbe_from_subblock : SBsyntax.subblock -> abes -> abes

val addrofbe_from_subblocks : SBsyntax.subblock list -> abes -> abes

val addrofbe_from_block : SBsyntax.block -> abes -> abes

val addrofbe_from_blocks : SBsyntax.blocks -> abes -> abes

val addrofbe_from_fdef : SBsyntax.fdef -> abes -> abes

type fabes = (LLVMsyntax.id*abes) list

val addrofbe_from_products : SBsyntax.products -> fabes -> fabes

val addrofbe_from_module : SBsyntax.coq_module -> fabes

