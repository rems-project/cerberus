open BinInt
open Datatypes
open Alist

module LLVMsyntax : 
 sig 
  val last_opt : 'a1 list -> 'a1 option
  
  module Size : 
   sig 
    type t = int
    
    val dec : t -> t -> bool
    
    val coq_Zero : t
    
    val coq_One : t
    
    val coq_Two : t
    
    val coq_Four : t
    
    val coq_Eight : t
    
    val coq_Sixteen : t
    
    val coq_ThirtyTwo : t
    
    val coq_SixtyFour : t
    
    val from_nat : nat -> t
    
    val to_nat : t -> nat
    
    val to_Z : t -> coq_Z
    
    val from_Z : coq_Z -> t
    
    val add : t -> t -> t
    
    val sub : t -> t -> t
    
    val mul : t -> t -> t
    
    val div : t -> t -> t
   end
  
  module Align : 
   sig 
    type t = int
    
    val dec : t -> t -> bool
    
    val coq_Zero : t
    
    val coq_One : t
    
    val coq_Two : t
    
    val coq_Four : t
    
    val coq_Eight : t
    
    val coq_Sixteen : t
    
    val coq_ThirtyTwo : t
    
    val coq_SixtyFour : t
    
    val from_nat : nat -> t
    
    val to_nat : t -> nat
    
    val to_Z : t -> coq_Z
    
    val from_Z : coq_Z -> t
    
    val add : t -> t -> t
    
    val sub : t -> t -> t
    
    val mul : t -> t -> t
    
    val div : t -> t -> t
   end
  
  module INTEGER : 
   sig 
    type t = Llvm.APInt.t
    
    val dec : t -> t -> bool
    
    val to_nat : t -> nat
    
    val to_Z : t -> coq_Z
    
    val of_Z : coq_Z -> coq_Z -> bool -> t
   end
  
  module FLOAT : 
   sig 
    type t = Llvm.APFloat.t
    
    val dec : t -> t -> bool
   end
  
  type coq_Int = INTEGER.t
  
  type coq_Float = FLOAT.t
  
  type sz = Size.t
  
  type id = String.t
  
  type l = String.t
  
  type align = Align.t
  
  type i = nat
  
  type floating_point =
    | Coq_fp_float
    | Coq_fp_double
    | Coq_fp_fp128
    | Coq_fp_x86_fp80
    | Coq_fp_ppc_fp128
  
  val floating_point_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> floating_point -> 'a1
  
  val floating_point_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> floating_point -> 'a1
  
  type varg = bool
  
  type typ =
    | Coq_typ_int of sz
    | Coq_typ_floatpoint of floating_point
    | Coq_typ_void
    | Coq_typ_label
    | Coq_typ_metadata
    | Coq_typ_array of sz * typ
    | Coq_typ_function of typ * list_typ * varg
    | Coq_typ_struct of list_typ
    | Coq_typ_pointer of typ
    | Coq_typ_opaque
    | Coq_typ_namedt of id
  and list_typ =
    | Nil_list_typ
    | Cons_list_typ of typ * list_typ
  
  val typ_rect :
    (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ
    -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> varg -> 'a1) -> (list_typ ->
    'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) -> typ -> 'a1
  
  val typ_rec :
    (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ
    -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> varg -> 'a1) -> (list_typ ->
    'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) -> typ -> 'a1
  
  val list_typ_rect :
    'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1
  
  val list_typ_rec :
    'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1
  
  type cond =
    | Coq_cond_eq
    | Coq_cond_ne
    | Coq_cond_ugt
    | Coq_cond_uge
    | Coq_cond_ult
    | Coq_cond_ule
    | Coq_cond_sgt
    | Coq_cond_sge
    | Coq_cond_slt
    | Coq_cond_sle
  
  val cond_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    cond -> 'a1
  
  val cond_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    cond -> 'a1
  
  type fcond =
    | Coq_fcond_false
    | Coq_fcond_oeq
    | Coq_fcond_ogt
    | Coq_fcond_oge
    | Coq_fcond_olt
    | Coq_fcond_ole
    | Coq_fcond_one
    | Coq_fcond_ord
    | Coq_fcond_ueq
    | Coq_fcond_ugt
    | Coq_fcond_uge
    | Coq_fcond_ult
    | Coq_fcond_ule
    | Coq_fcond_une
    | Coq_fcond_uno
    | Coq_fcond_true
  
  val fcond_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fcond -> 'a1
  
  val fcond_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fcond -> 'a1
  
  type bop =
    | Coq_bop_add
    | Coq_bop_sub
    | Coq_bop_mul
    | Coq_bop_udiv
    | Coq_bop_sdiv
    | Coq_bop_urem
    | Coq_bop_srem
    | Coq_bop_shl
    | Coq_bop_lshr
    | Coq_bop_ashr
    | Coq_bop_and
    | Coq_bop_or
    | Coq_bop_xor
  
  val bop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> bop -> 'a1
  
  val bop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> bop -> 'a1
  
  type fbop =
    | Coq_fbop_fadd
    | Coq_fbop_fsub
    | Coq_fbop_fmul
    | Coq_fbop_fdiv
    | Coq_fbop_frem
  
  val fbop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbop -> 'a1
  
  val fbop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbop -> 'a1
  
  type extop =
    | Coq_extop_z
    | Coq_extop_s
    | Coq_extop_fp
  
  val extop_rect : 'a1 -> 'a1 -> 'a1 -> extop -> 'a1
  
  val extop_rec : 'a1 -> 'a1 -> 'a1 -> extop -> 'a1
  
  type castop =
    | Coq_castop_fptoui
    | Coq_castop_fptosi
    | Coq_castop_uitofp
    | Coq_castop_sitofp
    | Coq_castop_ptrtoint
    | Coq_castop_inttoptr
    | Coq_castop_bitcast
  
  val castop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1
  
  val castop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1
  
  type inbounds = bool
  
  type truncop =
    | Coq_truncop_int
    | Coq_truncop_fp
  
  val truncop_rect : 'a1 -> 'a1 -> truncop -> 'a1
  
  val truncop_rec : 'a1 -> 'a1 -> truncop -> 'a1
  
  type const =
    | Coq_const_zeroinitializer of typ
    | Coq_const_int of sz * coq_Int
    | Coq_const_floatpoint of floating_point * coq_Float
    | Coq_const_undef of typ
    | Coq_const_null of typ
    | Coq_const_arr of typ * list_const
    | Coq_const_struct of list_const
    | Coq_const_gid of typ * id
    | Coq_const_truncop of truncop * const * typ
    | Coq_const_extop of extop * const * typ
    | Coq_const_castop of castop * const * typ
    | Coq_const_gep of inbounds * const * list_const
    | Coq_const_select of const * const * const
    | Coq_const_icmp of cond * const * const
    | Coq_const_fcmp of fcond * const * const
    | Coq_const_extractvalue of const * list_const
    | Coq_const_insertvalue of const * const * list_const
    | Coq_const_bop of bop * const * const
    | Coq_const_fbop of fbop * const * const
  and list_const =
    | Nil_list_const
    | Cons_list_const of const * list_const
  
  val const_rect :
    (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float ->
    'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a1) ->
    (list_const -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const -> 'a1 ->
    typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop -> const
    -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 -> list_const -> 'a1)
    -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (cond ->
    const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond -> const -> 'a1 -> const
    -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const -> 'a1) -> (const -> 'a1 ->
    const -> 'a1 -> list_const -> 'a1) -> (bop -> const -> 'a1 -> const ->
    'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const -> 'a1 -> 'a1) -> const ->
    'a1
  
  val const_rec :
    (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float ->
    'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a1) ->
    (list_const -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const -> 'a1 ->
    typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop -> const
    -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 -> list_const -> 'a1)
    -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (cond ->
    const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond -> const -> 'a1 -> const
    -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const -> 'a1) -> (const -> 'a1 ->
    const -> 'a1 -> list_const -> 'a1) -> (bop -> const -> 'a1 -> const ->
    'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const -> 'a1 -> 'a1) -> const ->
    'a1
  
  val list_const_rect :
    'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1
  
  val list_const_rec :
    'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1
  
  type attribute =
    | Coq_attribute_zext
    | Coq_attribute_sext
    | Coq_attribute_noreturn
    | Coq_attribute_inreg
    | Coq_attribute_structret
    | Coq_attribute_nounwind
    | Coq_attribute_noalias
    | Coq_attribute_byval
    | Coq_attribute_nest
    | Coq_attribute_readnone
    | Coq_attribute_readonly
    | Coq_attribute_noinline
    | Coq_attribute_alwaysinline
    | Coq_attribute_optforsize
    | Coq_attribute_stackprotect
    | Coq_attribute_stackprotectreq
    | Coq_attribute_nocapture
    | Coq_attribute_noredzone
    | Coq_attribute_implicitfloat
    | Coq_attribute_naked
  
  val attribute_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    attribute -> 'a1
  
  val attribute_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    attribute -> 'a1
  
  type value =
    | Coq_value_id of id
    | Coq_value_const of const
  
  val value_rect : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1
  
  val value_rec : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1
  
  type attributes = attribute list
  
  type param = (typ*attributes)*value
  
  type tailc = bool
  
  type callconv =
    | Coq_callconv_ccc
    | Coq_callconv_fast
    | Coq_callconv_cold
    | Coq_callconv_x86_stdcall
    | Coq_callconv_x86_fastcall
  
  val callconv_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> callconv -> 'a1
  
  val callconv_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> callconv -> 'a1
  
  type noret = bool
  
  type params = ((typ*attributes)*value) list
  
  type clattrs =
    | Coq_clattrs_intro of tailc * callconv * attributes * attributes
  
  val clattrs_rect :
    (tailc -> callconv -> attributes -> attributes -> 'a1) -> clattrs -> 'a1
  
  val clattrs_rec :
    (tailc -> callconv -> attributes -> attributes -> 'a1) -> clattrs -> 'a1
  
  type list_sz_value =
    | Nil_list_sz_value
    | Cons_list_sz_value of sz * value * list_sz_value
  
  val list_sz_value_rect :
    'a1 -> (sz -> value -> list_sz_value -> 'a1 -> 'a1) -> list_sz_value ->
    'a1
  
  val list_sz_value_rec :
    'a1 -> (sz -> value -> list_sz_value -> 'a1 -> 'a1) -> list_sz_value ->
    'a1
  
  type list_value_l =
    | Nil_list_value_l
    | Cons_list_value_l of value * l * list_value_l
  
  val list_value_l_rect :
    'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l -> 'a1
  
  val list_value_l_rec :
    'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l -> 'a1
  
  type cmd =
    | Coq_insn_bop of id * bop * sz * value * value
    | Coq_insn_fbop of id * fbop * floating_point * value * value
    | Coq_insn_extractvalue of id * typ * value * list_const
    | Coq_insn_insertvalue of id * typ * value * typ * value * list_const
    | Coq_insn_malloc of id * typ * value * align
    | Coq_insn_free of id * typ * value
    | Coq_insn_alloca of id * typ * value * align
    | Coq_insn_load of id * typ * value * align
    | Coq_insn_store of id * typ * value * value * align
    | Coq_insn_gep of id * inbounds * typ * value * list_sz_value
    | Coq_insn_trunc of id * truncop * typ * value * typ
    | Coq_insn_ext of id * extop * typ * value * typ
    | Coq_insn_cast of id * castop * typ * value * typ
    | Coq_insn_icmp of id * cond * typ * value * value
    | Coq_insn_fcmp of id * fcond * floating_point * value * value
    | Coq_insn_select of id * value * typ * value * value
    | Coq_insn_call of id * noret * clattrs * typ * value * params
  
  val cmd_rect :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> fbop ->
    floating_point -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value ->
    align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id ->
    inbounds -> typ -> value -> list_sz_value -> 'a1) -> (id -> truncop ->
    typ -> value -> typ -> 'a1) -> (id -> extop -> typ -> value -> typ ->
    'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond ->
    typ -> value -> value -> 'a1) -> (id -> fcond -> floating_point -> value
    -> value -> 'a1) -> (id -> value -> typ -> value -> value -> 'a1) -> (id
    -> noret -> clattrs -> typ -> value -> params -> 'a1) -> cmd -> 'a1
  
  val cmd_rec :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> fbop ->
    floating_point -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value ->
    align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id ->
    inbounds -> typ -> value -> list_sz_value -> 'a1) -> (id -> truncop ->
    typ -> value -> typ -> 'a1) -> (id -> extop -> typ -> value -> typ ->
    'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond ->
    typ -> value -> value -> 'a1) -> (id -> fcond -> floating_point -> value
    -> value -> 'a1) -> (id -> value -> typ -> value -> value -> 'a1) -> (id
    -> noret -> clattrs -> typ -> value -> params -> 'a1) -> cmd -> 'a1
  
  type phinode =
    | Coq_insn_phi of id * typ * list_value_l
  
  val phinode_rect : (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1
  
  val phinode_rec : (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1
  
  type arg = (typ*attributes)*id
  
  type visibility =
    | Coq_visibility_default
    | Coq_visibility_hidden
    | Coq_visibility_protected
  
  val visibility_rect : 'a1 -> 'a1 -> 'a1 -> visibility -> 'a1
  
  val visibility_rec : 'a1 -> 'a1 -> 'a1 -> visibility -> 'a1
  
  type linkage =
    | Coq_linkage_external
    | Coq_linkage_available_externally
    | Coq_linkage_link_once
    | Coq_linkage_link_once_odr
    | Coq_linkage_weak
    | Coq_linkage_weak_odr
    | Coq_linkage_appending
    | Coq_linkage_internal
    | Coq_linkage_private
    | Coq_linkage_linker_private
    | Coq_linkage_dllimport
    | Coq_linkage_dllexport
    | Coq_linkage_external_weak
    | Coq_linkage_ghost
    | Coq_linkage_common
  
  val linkage_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> linkage -> 'a1
  
  val linkage_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> linkage -> 'a1
  
  type terminator =
    | Coq_insn_return of id * typ * value
    | Coq_insn_return_void of id
    | Coq_insn_br of id * value * l * l
    | Coq_insn_br_uncond of id * l
    | Coq_insn_unreachable of id
  
  val terminator_rect :
    (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
    'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1
  
  val terminator_rec :
    (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
    'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1
  
  type cmds = cmd list
  
  type phinodes = phinode list
  
  type args = ((typ*attributes)*id) list
  
  type fnattrs =
    | Coq_fnattrs_intro of linkage * visibility * callconv * 
       attributes * attributes
  
  val fnattrs_rect :
    (linkage -> visibility -> callconv -> attributes -> attributes -> 'a1) ->
    fnattrs -> 'a1
  
  val fnattrs_rec :
    (linkage -> visibility -> callconv -> attributes -> attributes -> 'a1) ->
    fnattrs -> 'a1
  
  type block =
    | Coq_block_intro of l * phinodes * cmds * terminator
  
  val block_rect :
    (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1
  
  val block_rec :
    (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1
  
  type fheader =
    | Coq_fheader_intro of fnattrs * typ * id * args * varg
  
  val fheader_rect :
    (fnattrs -> typ -> id -> args -> varg -> 'a1) -> fheader -> 'a1
  
  val fheader_rec :
    (fnattrs -> typ -> id -> args -> varg -> 'a1) -> fheader -> 'a1
  
  type blocks = block list
  
  type gvar_spec =
    | Coq_gvar_spec_global
    | Coq_gvar_spec_constant
  
  val gvar_spec_rect : 'a1 -> 'a1 -> gvar_spec -> 'a1
  
  val gvar_spec_rec : 'a1 -> 'a1 -> gvar_spec -> 'a1
  
  type fdec =
    fheader
    (* singleton inductive, whose constructor was fdec_intro *)
  
  val fdec_rect : (fheader -> 'a1) -> fdec -> 'a1
  
  val fdec_rec : (fheader -> 'a1) -> fdec -> 'a1
  
  type fdef =
    | Coq_fdef_intro of fheader * blocks
  
  val fdef_rect : (fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  val fdef_rec : (fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  type gvar =
    | Coq_gvar_intro of id * linkage * gvar_spec * typ * const * align
    | Coq_gvar_external of id * gvar_spec * typ
  
  val gvar_rect :
    (id -> linkage -> gvar_spec -> typ -> const -> align -> 'a1) -> (id ->
    gvar_spec -> typ -> 'a1) -> gvar -> 'a1
  
  val gvar_rec :
    (id -> linkage -> gvar_spec -> typ -> const -> align -> 'a1) -> (id ->
    gvar_spec -> typ -> 'a1) -> gvar -> 'a1
  
  type layout =
    | Coq_layout_be
    | Coq_layout_le
    | Coq_layout_ptr of sz * align * align
    | Coq_layout_int of sz * align * align
    | Coq_layout_float of sz * align * align
    | Coq_layout_aggr of sz * align * align
    | Coq_layout_stack of sz * align * align
    | Coq_layout_vector of sz * align * align
  
  val layout_rect :
    'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
    'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
    (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) -> layout
    -> 'a1
  
  val layout_rec :
    'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
    'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
    (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) -> layout
    -> 'a1
  
  type namedt =
    | Coq_namedt_intro of id * typ
  
  val namedt_rect : (id -> typ -> 'a1) -> namedt -> 'a1
  
  val namedt_rec : (id -> typ -> 'a1) -> namedt -> 'a1
  
  type product =
    | Coq_product_gvar of gvar
    | Coq_product_fdec of fdec
    | Coq_product_fdef of fdef
  
  val product_rect :
    (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1
  
  val product_rec :
    (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1
  
  type layouts = layout list
  
  type namedts = namedt list
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of layouts * namedts * products
  
  val module_rect :
    (layouts -> namedts -> products -> 'a1) -> coq_module -> 'a1
  
  val module_rec :
    (layouts -> namedts -> products -> 'a1) -> coq_module -> 'a1
  
  type insn =
    | Coq_insn_phinode of phinode
    | Coq_insn_cmd of cmd
    | Coq_insn_terminator of terminator
  
  val insn_rect :
    (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1
  
  val insn_rec :
    (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1
  
  type modules = coq_module list
  
  type ids = id list
  
  type opt_Int = coq_Int option
  
  type opt_l = l option
  
  type opt_id = id option
  
  type opt_typ = typ option
  
  type opt_value = value option
  
  type ls = l list
  
  type insns = insn list
  
  type opt_block = block option
  
  type opt_fdec = fdec option
  
  type opt_fdef = fdef option
  
  type id_binding =
    | Coq_id_binding_none
    | Coq_id_binding_cmd of cmd
    | Coq_id_binding_phinode of phinode
    | Coq_id_binding_terminator of terminator
    | Coq_id_binding_gvar of gvar
    | Coq_id_binding_fdec of fdec
    | Coq_id_binding_arg of arg
  
  val id_binding_rect :
    'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
    -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1
  
  val id_binding_rec :
    'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
    -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1
  
  type targetdata = layout list*namedt list
  
  type system = modules
  
  type usedef_block = l list coq_AssocList
  
  type intrinsic_funs = ids
  
  val map_list_value_l : (value -> l -> 'a1) -> list_value_l -> 'a1 list
  
  val make_list_value_l : (value*l) list -> list_value_l
  
  val unmake_list_value_l : list_value_l -> (value*l) list
  
  val nth_list_value_l : nat -> list_value_l -> (value*l) option
  
  val app_list_value_l : list_value_l -> list_value_l -> list_value_l
  
  val map_list_sz_value : (sz -> value -> 'a1) -> list_sz_value -> 'a1 list
  
  val make_list_sz_value : (sz*value) list -> list_sz_value
  
  val unmake_list_sz_value : list_sz_value -> (sz*value) list
  
  val nth_list_sz_value : nat -> list_sz_value -> (sz*value) option
  
  val app_list_sz_value : list_sz_value -> list_sz_value -> list_sz_value
  
  val map_list_const : (const -> 'a1) -> list_const -> 'a1 list
  
  val make_list_const : const list -> list_const
  
  val unmake_list_const : list_const -> const list
  
  val nth_list_const : nat -> list_const -> const option
  
  val app_list_const : list_const -> list_const -> list_const
  
  val map_list_typ : (typ -> 'a1) -> list_typ -> 'a1 list
  
  val make_list_typ : typ list -> list_typ
  
  val unmake_list_typ : list_typ -> typ list
  
  val nth_list_typ : nat -> list_typ -> typ option
  
  val app_list_typ : list_typ -> list_typ -> list_typ
  
  val list_const_rec2 :
    (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float ->
    'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 -> 'a1)
    -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const
    -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop
    -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 -> list_const
    -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 -> 'a1)
    -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond -> const ->
    'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const -> 'a2 -> 'a1)
    -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 -> 'a1) -> (bop ->
    const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const ->
    'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) ->
    list_const -> 'a2
  
  val const_rec2 :
    (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float ->
    'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 -> 'a1)
    -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const
    -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop
    -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 -> list_const
    -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 -> 'a1)
    -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond -> const ->
    'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const -> 'a2 -> 'a1)
    -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 -> 'a1) -> (bop ->
    const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const ->
    'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> const
    -> 'a1
  
  val const_mutrec :
    (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float ->
    'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 -> 'a1)
    -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const
    -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop
    -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 -> list_const
    -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 -> 'a1)
    -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond -> const ->
    'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const -> 'a2 -> 'a1)
    -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 -> 'a1) -> (bop ->
    const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const ->
    'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) ->
    (const -> 'a1)*(list_const -> 'a2)
  
  val list_typ_rec2 :
    (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ
    -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
    (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) ->
    'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> list_typ -> 'a2
  
  val typ_rec2 :
    (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ
    -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
    (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) ->
    'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> typ -> 'a1
  
  val typ_mutrec :
    (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ
    -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
    (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) ->
    'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ -> 'a1)*(list_typ
    -> 'a2)
 end

