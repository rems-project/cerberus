open BinInt
open BinPos
open Bool
open Datatypes
open EqNat
open List0
open Peano
open Zpower
open Alist
open Infrastructure
open Monad
open Sub_symexe
open Sub_tv_dec
open Sub_tv_def
open Sub_tv_infer
open Syntax

val smem_lib_sub : LLVMsyntax.id -> bool

val load_from_metadata : SBSE.smem -> SBSE.sterm -> bool

val rename_id : LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id

val tv_id : LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool

val rename_fid : LLVMsyntax.id -> LLVMsyntax.id

val tv_fid : LLVMsyntax.id -> LLVMsyntax.id -> bool

val tv_const : LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const -> bool

val tv_list_const :
  LLVMsyntax.id -> LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool

val tv_value : LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value -> bool

val syscall_returns_pointer : LLVMsyntax.id -> bool

val rename_fid_inv : LLVMsyntax.id -> LLVMsyntax.id option

val function_returns_pointer : LLVMsyntax.products -> LLVMsyntax.id -> bool

val store_to_ret :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sterm ->
  bool

val tv_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sterm ->
  SBSE.sterm -> bool

val tv_list_sz_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  SBSE.list_sz_sterm -> SBSE.list_sz_sterm -> bool

val tv_list_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  SBSE.list_sterm -> SBSE.list_sterm -> bool

val tv_list_sterm_l :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  SBSE.list_sterm_l -> SBSE.list_sterm_l -> bool

val tv_smem :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.smem ->
  SBSE.smem -> bool

val tv_sframe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sframe ->
  SBSE.sframe -> bool

val tv_smap :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.smap ->
  SBSE.smap -> bool

val sub_sstate :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sstate ->
  SBSE.sstate -> bool

val tv_cmds :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.nbranch
  list -> SBSE.nbranch list -> bool

val tv_sparams :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> bool

type scall =
  | Coq_stmn_call of LLVMsyntax.id * LLVMsyntax.noret * 
     LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list

val scall_rect :
  (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ
  -> SBSE.sterm -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  -> 'a1) -> scall -> 'a1

val scall_rec :
  (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ
  -> SBSE.sterm -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  -> 'a1) -> scall -> 'a1

val se_call : SBSE.sstate -> LLVMsyntax.cmd -> scall

val tv_scall :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> scall ->
  sicall -> bool

val tv_subblock :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.subblock
  -> SBsyntax.subblock -> bool

val tv_subblocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.subblock
  list -> SBsyntax.subblock list -> bool

val tv_list_value_l :
  LLVMsyntax.id -> LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool

val tv_phinode :
  LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool

val tv_phinodes :
  LLVMsyntax.id -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool

val tv_terminator :
  LLVMsyntax.id -> LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool

val tv_block :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  LLVMsyntax.block -> SBsyntax.block -> bool

val tv_blocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  LLVMsyntax.blocks -> SBsyntax.blocks -> bool

val tv_fheader :
  LLVMsyntax.namedt list -> LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool

val tv_fdec :
  LLVMsyntax.namedt list -> LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool

val tv_fdef :
  LLVMsyntax.namedt list -> LLVMsyntax.products -> SBsyntax.products ->
  LLVMsyntax.fdef -> SBsyntax.fdef -> bool

val tv_products :
  LLVMsyntax.namedt list -> LLVMsyntax.products -> LLVMsyntax.products ->
  SBsyntax.products -> bool

val tv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool

val tv_system : LLVMsyntax.system -> SBsyntax.system -> bool

val rtv_const : LLVMsyntax.const -> LLVMsyntax.const -> bool

val rtv_list_const : LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool

type renaming = (LLVMsyntax.id*LLVMsyntax.id) list

val is_tmp_var : LLVMsyntax.id -> bool

val lookup_renaming :
  LLVMsyntax.id coq_AssocList -> LLVMsyntax.id -> LLVMsyntax.id option

val rtv_id : renaming -> LLVMsyntax.id -> LLVMsyntax.id -> bool

val rtv_value :
  LLVMsyntax.id coq_AssocList -> LLVMsyntax.value -> LLVMsyntax.value ->
  renaming option

val rtv_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id
  coq_AssocList -> SBSE.sterm -> SBSE.sterm -> renaming option

val rtv_list_sz_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.list_sz_sterm -> SBSE.list_sz_sterm -> renaming option

val rtv_list_sterm :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.list_sterm -> SBSE.list_sterm -> renaming option

val rtv_list_sterm_l :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id
  coq_AssocList -> SBSE.list_sterm_l -> SBSE.list_sterm_l -> renaming option

val rtv_smem :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id
  coq_AssocList -> SBSE.smem -> SBSE.smem -> renaming option

val rtv_sframe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.sframe -> SBSE.sframe -> renaming option

val match_smap :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id
  coq_AssocList -> LLVMsyntax.id -> SBSE.sterm -> (LLVMsyntax.id*SBSE.sterm)
  list -> renaming option

val rtv_smap :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.smap -> SBSE.smap -> renaming option

val rsub_sstate :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.sstate -> SBSE.sstate -> renaming option

val rtv_cmds :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.nbranch list -> SBSE.nbranch list -> renaming option

val rtv_sparams :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list ->
  ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> renaming option

val rtv_scall :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  scall -> sicall -> renaming option

val rtv_subblock :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.subblock -> SBsyntax.subblock -> renaming option

val rtv_subblocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  SBSE.subblock list -> SBsyntax.subblock list -> renaming option

val rtv_list_value_l :
  renaming -> LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> renaming
  option

val rtv_phinode :
  renaming -> LLVMsyntax.typ -> LLVMsyntax.list_value_l -> LLVMsyntax.typ ->
  LLVMsyntax.list_value_l -> renaming option

val match_phinodes :
  renaming -> LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_value_l ->
  LLVMsyntax.phinode list -> (LLVMsyntax.phinodes*renaming) option

val rtv_phinodes :
  renaming -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> renaming option

val rtv_terminator :
  LLVMsyntax.id coq_AssocList -> LLVMsyntax.terminator ->
  LLVMsyntax.terminator -> renaming option

val rtv_block :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  LLVMsyntax.block -> SBsyntax.block -> renaming option

val rtv_blocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
  LLVMsyntax.blocks -> SBsyntax.blocks -> renaming option

val rtv_fdef :
  LLVMsyntax.namedt list -> LLVMsyntax.products -> SBsyntax.products ->
  LLVMsyntax.fdef -> SBsyntax.fdef -> bool

val rtv_products :
  LLVMsyntax.namedt list -> LLVMsyntax.products -> LLVMsyntax.products ->
  SBsyntax.products -> bool

val rtv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool

val deref_from_metadata :
  LLVMsyntax.id -> SBSE.smem -> SBSE.sterm -> SBSE.sterm -> SBSE.sterm ->
  bool

type metadata =
  ((((((LLVMsyntax.id*LLVMsyntax.l)*nat)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*bool)
  list

val is_metadata_aux :
  metadata -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> LLVMsyntax.id ->
  LLVMsyntax.id -> LLVMsyntax.id -> bool -> bool

val get_metadata : unit -> metadata

val is_metadata :
  LLVMsyntax.id -> LLVMsyntax.l -> nat -> LLVMsyntax.id -> LLVMsyntax.id ->
  LLVMsyntax.id -> bool -> bool

val check_mptr_metadata_aux :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm ->
  SBSE.sterm -> SBSE.sterm -> bool

val check_mptr_metadata :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm ->
  SBSE.sterm -> SBSE.sterm -> bool

val check_fptr_metadata_aux :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm ->
  SBSE.sterm -> SBSE.sterm -> bool

val check_fptr_metadata :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm ->
  SBSE.sterm -> SBSE.sterm -> bool

val check_metadata :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm ->
  SBSE.sterm -> SBSE.sterm -> bool -> bool

val deref_check :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> LLVMsyntax.id
  -> SBSE.list_sterm -> bool

val find_stored_ptr : SBSE.smem -> SBSE.sterm -> SBSE.sterm option

val store_to_metadata :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smem ->
  LLVMsyntax.id -> SBSE.list_sterm -> bool

val get_addrof_be :
  unit -> ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) list

val is_addrof_be_aux :
  ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) list -> LLVMsyntax.id ->
  LLVMsyntax.id -> LLVMsyntax.id -> bool

val is_addrof_be : LLVMsyntax.id -> SBSE.sterm -> SBSE.sterm -> bool

val safe_mem_access :
  LLVMsyntax.id -> SBSE.smem -> LLVMsyntax.typ -> SBSE.sterm -> bool

val sterm_is_memsafe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBSE.sterm -> bool

val list_sz_sterm_is_memsafe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBSE.list_sz_sterm -> bool

val list_sterm_is_memsafe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBSE.list_sterm -> bool

val list_sterm_l_is_memsafe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBSE.list_sterm_l -> bool

val smem_is_memsafe :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBSE.smem -> bool

val check_all_metadata_aux :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smap ->
  metadata -> bool

val check_all_metadata :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smap ->
  bool

val check_addrof_be_aux :
  LLVMsyntax.id -> SBSE.smap -> ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id)
  list -> bool

val check_addrof_be : LLVMsyntax.id -> SBSE.smap -> bool

val mtv_cmds :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> SBSE.nbranch list -> bool

val mtv_func_metadata :
  metadata -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat ->
  LLVMsyntax.id -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id)
  list -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> bool

val safe_fptr_access_aux : SBSE.smem -> SBSE.sterm -> bool

val safe_fptr_access : SBSE.smem -> SBSE.sterm -> bool

val mtv_iscall :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smem ->
  sicall -> bool

val mtv_subblock :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBsyntax.subblock -> bool

val mtv_subblocks_aux :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> nat -> SBsyntax.subblock list -> bool

val mtv_subblocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
  -> SBsyntax.subblock list -> bool

val mtv_bep_value :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> LLVMsyntax.value ->
  LLVMsyntax.value -> LLVMsyntax.value -> bool -> bool

val mtv_list_value_l :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.list_value_l ->
  LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool -> bool

val mtv_phinodes_aux :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> metadata ->
  LLVMsyntax.phinodes -> bool

val mtv_phinodes :
  SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat ->
  LLVMsyntax.phinodes -> bool

val mtv_block :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBsyntax.block
  -> bool

val mtv_blocks :
  LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
  SBsyntax.blocks -> bool

val mtv_fdef :
  LLVMsyntax.products -> SBsyntax.products -> SBsyntax.fdef -> bool

val mtv_products :
  LLVMsyntax.products -> SBsyntax.products -> SBsyntax.products -> bool

val mtv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool

