open Lem_pervasives

open Ctype
open Annot
open Loc
open Mem
open Mem_common
open Core_aux

open Lem_assert_extra



type symbol = Symbol.sym
type mu_object_type = Core.core_object_type
type mu_base_type = Core.core_base_type
type mu_name = symbol Core.generic_name

type ('o, 'bty) a = A of Annot.annot list * 'bty * 'o

let a_unpack (A (_, _, a)) = a
let a_pack annots2 bty a = A (annots2, bty, a)

type 'bty asym = (Symbol.sym, 'bty) a
type 'bty asyms = ('bty asym) list

type 'bty ov_asym = 'bty asym       (* object_value *)
type 'bty lv_asym = 'bty asym       (* loaded_value *)
type 'bty va_asym = 'bty asym       (* value *)







type ('DCTY, 'bty) mu_object_value =  (* C object values *)
 | M_OVinteger of Impl_mem.integer_value (* integer value *)
 | M_OVfloating of Impl_mem.floating_value (* floating-point value *)
 | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
 | M_OVarray of ('bty lv_asym) list (* C array value *)
 | M_OVstruct of symbol * (Symbol.identifier * 'DCTY * Impl_mem.mem_value) list (* C struct value *)
 | M_OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)


type ('DCTY, 'bty) mu_loaded_value =  (* potentially unspecified C object values *)
 | M_LVspecified of ('DCTY, 'bty) mu_object_value (* non-unspecified loaded value *)


(* again, we might remove something from the definition here,
   e.g. Vctype *)
type ('DCTY, 'DBTY, 'bty) mu_value =  (* Core values *)
 | M_Vobject of ('DCTY, 'bty) mu_object_value (* C object value *)
 | M_Vloaded of ('DCTY, 'bty) mu_loaded_value (* loaded C object value *)
 | M_Vunit
 | M_Vtrue
 | M_Vfalse
 | M_Vlist of 'DBTY * ('bty asym) list
 | M_Vtuple of ('bty asym) list (* tuple *)



type 'DBTY mu_ctor =  (* data constructors *)
 | M_Cnil of 'DBTY (* empty list *) 
 (* annotated with the type of the list items *)
 | M_Ccons (* list cons *)
 | M_Ctuple (* tuple *)
 | M_Carray (* C array *)
 | M_CivCOMPL (* bitwise complement *)
 | M_CivAND (* bitwise AND *)
 | M_CivOR (* bitwise OR *)
 | M_CivXOR (* bitwise XOR *)
 | M_Cspecified (* non-unspecified loaded value *)
 | M_Cfvfromint (* cast integer to floating value *)
 | M_Civfromfloat (* cast floating to integer value *)

type 'DBTY mu_pattern_ = 
 | M_CaseBase of (Symbol.sym option * 'DBTY)
 | M_CaseCtor of 'DBTY mu_ctor * ('DBTY mu_pattern) list

and 'DBTY mu_pattern = 
 | M_Pattern of annot list * ('DBTY mu_pattern_)

type ('DBTY, 'bty) mu_sym_or_pattern = 
  | M_Symbol of symbol
  | M_Pat of 'DBTY mu_pattern

type ('DCTY, 'DBTY, 'bty) mu_pexpr_ =  (* Core pure expressions *)
 | M_PEsym of symbol
 | M_PEimpl of Implementation.implementation_constant (* implementation-defined constant *)
 | M_PEval of ('DCTY, 'DBTY, 'bty) mu_value
 | M_PEconstrained of (Mem.mem_iv_constraint * 'bty asym) list (* constrained value *)
 | M_PEundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_PEerror of string * 'bty asym (* impl-defined static error *)
 | M_PEctor of 'DBTY mu_ctor * ('bty asym) list (* data constructor application *)
 | M_PEcase of ('bty asym) * ('DBTY mu_pattern * ('DCTY, 'DBTY, 'bty) mu_pexpr) list (* pattern matching *)
 | M_PEarray_shift of ('bty asym) * 'DCTY * ('bty asym) (* pointer array shift *)
 | M_PEmember_shift of ('bty asym) * symbol * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'bty asym (* boolean not *)
 | M_PEop of Core.binop * ('bty asym) * ('bty asym)
 | M_PEstruct of symbol * (Symbol.identifier * 'bty asym) list (* C struct expression *)
 | M_PEunion of symbol * Symbol.identifier * 'bty asym (* C union expression *)
 | M_PEmemberof of symbol * Symbol.identifier * 'bty asym (* C struct/union member access *)
 | M_PEcall of mu_name * ('bty asym) list (* pure function call *)
 | M_PElet of (('DBTY, 'bty) mu_sym_or_pattern) * (('DCTY, 'DBTY, 'bty) mu_pexpr) * (('DCTY, 'DBTY, 'bty) mu_pexpr) (* pure let *)
 | M_PEif of 'bty asym * (('DCTY, 'DBTY, 'bty) mu_pexpr) * (('DCTY, 'DBTY, 'bty) mu_pexpr) (* pure if *)


and ('DCTY, 'DBTY, 'bty) mu_pexpr = 
 | M_Pexpr of annot list * 'bty * (('DCTY, 'DBTY, 'bty) mu_pexpr_)



type 'DCTY m_kill_kind = 
  | M_Dynamic
  | M_Static of 'DCTY

type ('DCTY, 'bty) mu_action_ =  (* memory actions *)
 | M_Create of 'bty asym * (('DCTY, 'bty) a) * Symbol.prefix
 | M_CreateReadOnly of 'bty asym * (('DCTY, 'bty) a) * 'bty asym * Symbol.prefix
 | M_Alloc of (('DCTY, 'bty) a) * 'bty asym * Symbol.prefix
 | M_Kill of 'DCTY m_kill_kind * 'bty asym (* the boolean indicates whether the action is dynamic (i.e. free()) *)
 | M_Store of bool * (('DCTY, 'bty) a) * 'bty asym * 'bty asym * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
 | M_Load of (('DCTY, 'bty) a) * 'bty asym * Cmm_csem.memory_order
 | M_RMW of (('DCTY, 'bty) a) * 'bty asym * 'bty asym * 'bty asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of (('DCTY, 'bty) a) * 'bty asym * 'bty asym * 'bty asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of (('DCTY, 'bty) a) * 'bty asym * 'bty asym * 'bty asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of (('DCTY, 'bty) a) * 'bty asym * Linux.linux_memory_order
 | M_LinuxStore of (('DCTY, 'bty) a) * 'bty asym * 'bty asym * Linux.linux_memory_order
 | M_LinuxRMW of (('DCTY, 'bty) a) * 'bty asym * 'bty asym * Linux.linux_memory_order


type ('DCTY, 'bty) mu_action = 
 | M_Action of Location_ocaml.t * (('DCTY, 'bty) mu_action_)


type ('DCTY, 'bty) mu_paction =  (* memory actions with Core.polarity *)
 | M_Paction of Core.polarity * (('DCTY, 'bty) mu_action)

type ('DCTY, 'bty) mu_memop =
  | M_PtrEq of ('bty asym * 'bty asym)
  | M_PtrNe of ('bty asym * 'bty asym)
  | M_PtrLt of ('bty asym * 'bty asym)
  | M_PtrGt of ('bty asym * 'bty asym)
  | M_PtrLe of ('bty asym * 'bty asym)
  | M_PtrGe of ('bty asym * 'bty asym)
  | M_Ptrdiff of ((('DCTY, 'bty) a) * 'bty asym * 'bty asym)
  | M_IntFromPtr of ((('DCTY, 'bty) a) * 'bty asym)
  | M_PtrFromInt of ((('DCTY, 'bty) a) * 'bty asym)
  | M_PtrValidForDeref of ((('DCTY, 'bty) a) * 'bty asym)
  | M_PtrWellAligned of ((('DCTY, 'bty) a) * 'bty asym)
  | M_PtrArrayShift of ('bty asym * (('DCTY, 'bty) a) * 'bty asym)
  | M_Memcpy of ('bty asym * 'bty asym * 'bty asym)
  | M_Memcmp of ('bty asym * 'bty asym * 'bty asym)
  | M_Realloc of ('bty asym * 'bty asym * 'bty asym)
  | M_Va_start  of ('bty asym * 'bty asym)
  | M_Va_copy of ('bty asym)
  | M_Va_arg of ('bty asym * (('DCTY, 'bty) a))
  | M_Va_end of ('bty asym)


type ('DCTY, 'DBTY, 'bty) mu_expr_ =  (* (effectful) expression *)
 | M_Epure of (('DCTY, 'DBTY, 'bty) mu_pexpr)
 | M_Ememop of ('DCTY, 'bty) mu_memop
 | M_Eaction of (('DCTY, 'bty) mu_paction) (* memory action *)
 | M_Ecase of 'bty asym * ('DBTY mu_pattern * (('DCTY, 'DBTY, 'bty) mu_expr)) list (* pattern matching *)
 | M_Elet of (('DBTY, 'bty) mu_sym_or_pattern) * (('DCTY, 'DBTY, 'bty) mu_pexpr) * (('DCTY, 'DBTY, 'bty) mu_expr)
 | M_Eif of 'bty asym * (('DCTY, 'DBTY, 'bty) mu_expr) * (('DCTY, 'DBTY, 'bty) mu_expr)
 | M_Eskip
 | M_Eccall of ((('DCTY, 'bty) a)) * 'bty asym * ('bty asym) list (* C function call *)
 | M_Eproc of mu_name * ('bty asym) list (* Core procedure call *)
 | M_Ewseq of 'DBTY mu_pattern * (('DCTY, 'DBTY, 'bty) mu_expr) * (('DCTY, 'DBTY, 'bty) mu_expr) (* weak sequencing *)
 | M_Esseq of 'DBTY mu_pattern * (('DCTY, 'DBTY, 'bty) mu_expr) * (('DCTY, 'DBTY, 'bty) mu_expr) (* strong sequencing *)
 | M_Ebound of int * (('DCTY, 'DBTY, 'bty) mu_expr) (* $\ldots$and boundary *)
 | M_End of (('DCTY, 'DBTY, 'bty) mu_expr) list (* nondeterministic choice *)
 | M_Erun of symbol * ('bty asym) list (* run from label *)

and ('DCTY, 'DBTY, 'bty) mu_expr = 
 | M_Expr of annot list * (('DCTY, 'DBTY, 'bty) mu_expr_)




let embed_pexpr_expr pe : ('c,'b,'a) mu_expr= 
  let (M_Pexpr (annots2, _bty, _)) = pe in
  M_Expr (annots2, (M_Epure pe))


type ('DCTY, 'DBTY, 'bty) mu_impl_decl =
  | M_Def of 'DBTY * ('DCTY, 'DBTY, 'bty) mu_pexpr
  | M_IFun of 'DBTY * (symbol * 'DBTY) list * ('DCTY, 'DBTY, 'bty) mu_pexpr

type ('DCTY, 'DBTY, 'bty) mu_impl = (Implementation.implementation_constant, (('DCTY, 'DBTY, 'bty) mu_impl_decl)) 
  Pmap.map

type ('DLTY, 'DCTY, 'DBTY, 'bty) mu_label_def = 
  | M_Return of 'DLTY
  | M_Label of 'DLTY * ((symbol * 'DBTY) list) * ('DCTY, 'DBTY, 'bty) mu_expr * annot list

type ('DLTY, 'DCTY, 'DBTY, 'bty) mu_label_defs = (symbol, (('DLTY, 'DCTY, 'DBTY, 'bty) mu_label_def))
  Pmap.map


type ('DLTY, 'DCTY, 'DBTY, 'bty) mu_fun_map_decl =
  | M_Fun of 'DBTY * (symbol * 'DBTY) list * ('DCTY, 'DBTY, 'bty) mu_pexpr
  | M_Proc of Location_ocaml.t * 'DBTY * (symbol * 'DBTY) list * ('DCTY, 'DBTY, 'bty) mu_expr * ('DLTY, 'DCTY, 'DBTY, 'bty) mu_label_defs
  | M_ProcDecl of Location_ocaml.t * 'DBTY * 'DBTY list
  | M_BuiltinDecl of Location_ocaml.t * 'DBTY * 'DBTY list

type ('DLTY, 'DCTY, 'DBTY, 'bty) mu_fun_map = (symbol, (('DLTY, 'DCTY, 'DBTY, 'bty) mu_fun_map_decl)) 
  Pmap.map



type mu_linking_kind = Core.linking_kind

type mu_extern_map = Core.extern_map

type ('DCTY, 'DBTY, 'bty) mu_globs =
  | M_GlobalDef of 'DBTY * ('DCTY, 'DBTY, 'bty) mu_expr
  | M_GlobalDecl of 'DBTY

type ('DCTY, 'DBTY, 'bty) mu_globs_map = (symbol, (('DCTY, 'DBTY, 'bty) mu_globs))
  Pmap.map



type 'DCTY mu_struct_def = (Symbol.identifier * (Annot.attributes * qualifiers * 'DCTY)) list *  flexible_array_member option
type 'DCTY mu_union_def = (Symbol.identifier * (Annot.attributes * qualifiers * 'DCTY)) list

type ('DSTRUCT_DEF, 'DUNION_DEF) mu_tag_definition =
  | M_StructDef of 'DSTRUCT_DEF
  | M_UnionDef of 'DUNION_DEF

type ('DSTRUCT_DEF, 'DUNION_DEF) mu_tag_definitions = (Symbol.sym, (('DSTRUCT_DEF, 'DUNION_DEF) mu_tag_definition)) 
  Pmap.map

type 'DCTY mu_funinfo_type = 'DCTY * (symbol option * 'DCTY) list

type 'DFTY mu_funinfo = 
  M_funinfo of (Location_ocaml.t * Annot.attributes * 'DFTY * bool * bool)

type 'DFTY mu_funinfos = (symbol, ('DFTY mu_funinfo)) Pmap.map

type ('DCTY, 'DBTY, 'bty) mu_globs_list = (symbol * ('DCTY, 'DBTY, 'bty) mu_globs) list

(* a Core file is just a set of named functions *)
type ('DFTY, 'DLTY, 'DCTY, 'DBTY, 'DSTRUCT_DEF, 'DUNION_DEF, 'bty) mu_file = {
  mu_main    : symbol option;
  mu_tagDefs : ('DSTRUCT_DEF, 'DUNION_DEF) mu_tag_definitions;
  mu_core_tagDefs : Core.core_tag_definitions;
  mu_stdlib  : ('DLTY, 'DCTY, 'DBTY, 'bty) mu_fun_map;
  mu_impl    : ('DCTY, 'DBTY, 'bty) mu_impl;
  mu_globs   : ('DCTY, 'DBTY, 'bty) mu_globs_list;
  mu_funs    : ('DLTY, 'DCTY, 'DBTY, 'bty) mu_fun_map;
  mu_extern  : mu_extern_map;
  mu_funinfo : 'DFTY mu_funinfos;
  mu_loop_attributes : Annot.loop_attributes;
}


