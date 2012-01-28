open Bool
open MetatheoryAtom
open Infrastructure
open Symexe_def
open Syntax

type sterm_dec_prop = SimpleSE.sterm -> bool

type list_sterm_dec_prop = SimpleSE.list_sterm -> bool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> bool

type smem_dec_prop = SimpleSE.smem -> bool

type sframe_dec_prop = SimpleSE.sframe -> bool

val se_dec :
  ((((SimpleSE.sterm -> sterm_dec_prop)*(SimpleSE.list_sterm ->
  list_sterm_dec_prop))*(SimpleSE.list_sterm_l ->
  list_sterm_l_dec_prop))*(SimpleSE.smem -> smem_dec_prop))*(SimpleSE.sframe
  -> sframe_dec_prop)

val sterm_dec : SimpleSE.sterm -> SimpleSE.sterm -> bool

val list_sterm_dec : SimpleSE.list_sterm -> SimpleSE.list_sterm -> bool

val list_sterm_l_dec : SimpleSE.list_sterm_l -> SimpleSE.list_sterm_l -> bool

val smem_dec : SimpleSE.smem -> SimpleSE.smem -> bool

val sframe_dec : SimpleSE.sframe -> SimpleSE.sframe -> bool

val sterminator_dec : SimpleSE.sterminator -> SimpleSE.sterminator -> bool

val list_typ_sterm_dec :
  (LLVMsyntax.typ*SimpleSE.sterm) list -> (LLVMsyntax.typ*SimpleSE.sterm)
  list -> bool

val smap_dec : SimpleSE.smap -> SimpleSE.smap -> bool

val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> bool

val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> bool

