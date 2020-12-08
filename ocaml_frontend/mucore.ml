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

type ('o, 'TY) a = 
  { annot: Annot.annot list;
    type_annot : 'TY;
    item: 'o }

let a_unpack a = 
  (a.annot, a.type_annot, a.item)
let a_pack annot type_annot item = 
  {annot; type_annot; item}

type 'TY asym = (Symbol.sym, 'TY) a
type 'TY asyms = ('TY asym) list

type 'TY ov_asym = 'TY asym       (* object_value *)
type 'TY lv_asym = 'TY asym       (* loaded_value *)
type 'TY va_asym = 'TY asym       (* value *)







type ('ct, 'TY) mu_object_value =  (* C object values *)
 | M_OVinteger of Impl_mem.integer_value (* integer value *)
 | M_OVfloating of Impl_mem.floating_value (* floating-point value *)
 | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
 | M_OVarray of ('TY lv_asym) list (* C array value *)
 | M_OVstruct of symbol * (Symbol.identifier * 'ct * Impl_mem.mem_value) list (* C struct value *)
 | M_OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)


type ('ct, 'TY) mu_loaded_value =  (* potentially unspecified C object values *)
 | M_LVspecified of ('ct, 'TY) mu_object_value (* non-unspecified loaded value *)


(* again, we might remove something from the definition here,
   e.g. Vctype *)
type ('ct, 'bt, 'TY) mu_value =  (* Core values *)
 | M_Vobject of ('ct, 'TY) mu_object_value (* C object value *)
 | M_Vloaded of ('ct, 'TY) mu_loaded_value (* loaded C object value *)
 | M_Vunit
 | M_Vtrue
 | M_Vfalse
 | M_Vlist of 'bt * ('TY asym) list
 | M_Vtuple of ('TY asym) list (* tuple *)



type 'bt mu_ctor =  (* data constructors *)
 | M_Cnil of 'bt (* empty list *) 
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

type 'bt mu_pattern_ = 
 | M_CaseBase of (Symbol.sym option * 'bt)
 | M_CaseCtor of 'bt mu_ctor * ('bt mu_pattern) list

and 'bt mu_pattern = 
 | M_Pattern of annot list * ('bt mu_pattern_)

type ('bt, 'TY) mu_sym_or_pattern = 
  | M_Symbol of symbol
  | M_Pat of 'bt mu_pattern

type ('ct, 'bt, 'TY) mu_pexpr_ =  (* Core pure expressions *)
 | M_PEsym of symbol
 | M_PEimpl of Implementation.implementation_constant (* implementation-defined constant *)
 | M_PEval of ('ct, 'bt, 'TY) mu_value
 | M_PEconstrained of (Mem.mem_iv_constraint * 'TY asym) list (* constrained value *)
 | M_PEundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_PEerror of string * 'TY asym (* impl-defined static error *)
 | M_PEctor of 'bt mu_ctor * ('TY asym) list (* data constructor application *)
 | M_PEcase of ('TY asym) * ('bt mu_pattern * ('ct, 'bt, 'TY) mu_pexpr) list (* pattern matching *)
 | M_PEarray_shift of ('TY asym) * 'ct * ('TY asym) (* pointer array shift *)
 | M_PEmember_shift of ('TY asym) * symbol * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'TY asym (* boolean not *)
 | M_PEop of Core.binop * ('TY asym) * ('TY asym)
 | M_PEstruct of symbol * (Symbol.identifier * 'TY asym) list (* C struct expression *)
 | M_PEunion of symbol * Symbol.identifier * 'TY asym (* C union expression *)
 | M_PEmemberof of symbol * Symbol.identifier * 'TY asym (* C struct/union member access *)
 | M_PEcall of mu_name * ('TY asym) list (* pure function call *)
 | M_PElet of (('bt, 'TY) mu_sym_or_pattern) * (('ct, 'bt, 'TY) mu_pexpr) * (('ct, 'bt, 'TY) mu_pexpr) (* pure let *)
 | M_PEif of 'TY asym * (('ct, 'bt, 'TY) mu_pexpr) * (('ct, 'bt, 'TY) mu_pexpr) (* pure if *)


and ('ct, 'bt, 'TY) mu_pexpr = 
 | M_Pexpr of annot list * 'TY * (('ct, 'bt, 'TY) mu_pexpr_)



type 'ct m_kill_kind = 
  | M_Dynamic
  | M_Static of 'ct

type ('ct, 'TY) mu_action_ =  (* memory actions *)
 | M_Create of 'TY asym * (('ct, 'TY) a) * Symbol.prefix
 | M_CreateReadOnly of 'TY asym * (('ct, 'TY) a) * 'TY asym * Symbol.prefix
 | M_Alloc of 'TY asym * 'TY asym * Symbol.prefix
 | M_Kill of 'ct m_kill_kind * 'TY asym (* the boolean indicates whether the action is dynamic (i.e. free()) *)
 | M_Store of bool * (('ct, 'TY) a) * 'TY asym * 'TY asym * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
 | M_Load of (('ct, 'TY) a) * 'TY asym * Cmm_csem.memory_order
 | M_RMW of (('ct, 'TY) a) * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of (('ct, 'TY) a) * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of (('ct, 'TY) a) * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of (('ct, 'TY) a) * 'TY asym * Linux.linux_memory_order
 | M_LinuxStore of (('ct, 'TY) a) * 'TY asym * 'TY asym * Linux.linux_memory_order
 | M_LinuxRMW of (('ct, 'TY) a) * 'TY asym * 'TY asym * Linux.linux_memory_order


type ('ct, 'TY) mu_action = 
 | M_Action of Location_ocaml.t * (('ct, 'TY) mu_action_)


type ('ct, 'TY) mu_paction =  (* memory actions with Core.polarity *)
 | M_Paction of Core.polarity * (('ct, 'TY) mu_action)

type ('ct, 'TY) mu_memop =
  | M_PtrEq of ('TY asym * 'TY asym)
  | M_PtrNe of ('TY asym * 'TY asym)
  | M_PtrLt of ('TY asym * 'TY asym)
  | M_PtrGt of ('TY asym * 'TY asym)
  | M_PtrLe of ('TY asym * 'TY asym)
  | M_PtrGe of ('TY asym * 'TY asym)
  | M_Ptrdiff of ((('ct, 'TY) a) * 'TY asym * 'TY asym)
  | M_IntFromPtr of ((('ct, 'TY) a) * 'TY asym)
  | M_PtrFromInt of ((('ct, 'TY) a) * (('ct, 'TY) a) * 'TY asym)
  | M_PtrValidForDeref of ((('ct, 'TY) a) * 'TY asym)
  | M_PtrWellAligned of ((('ct, 'TY) a) * 'TY asym)
  | M_PtrArrayShift of ('TY asym * (('ct, 'TY) a) * 'TY asym)
  | M_Memcpy of ('TY asym * 'TY asym * 'TY asym)
  | M_Memcmp of ('TY asym * 'TY asym * 'TY asym)
  | M_Realloc of ('TY asym * 'TY asym * 'TY asym)
  | M_Va_start  of ('TY asym * 'TY asym)
  | M_Va_copy of ('TY asym)
  | M_Va_arg of ('TY asym * (('ct, 'TY) a))
  | M_Va_end of ('TY asym)


type ('ct, 'bt, 'TY) mu_expr_ =  (* (effectful) expression *)
 | M_Epure of (('ct, 'bt, 'TY) mu_pexpr)
 | M_Ememop of ('ct, 'TY) mu_memop
 | M_Eaction of (('ct, 'TY) mu_paction) (* memory action *)
 | M_Ecase of 'TY asym * ('bt mu_pattern * (('ct, 'bt, 'TY) mu_expr)) list (* pattern matching *)
 | M_Elet of (('bt, 'TY) mu_sym_or_pattern) * (('ct, 'bt, 'TY) mu_pexpr) * (('ct, 'bt, 'TY) mu_expr)
 | M_Eif of 'TY asym * (('ct, 'bt, 'TY) mu_expr) * (('ct, 'bt, 'TY) mu_expr)
 | M_Eskip
 | M_Eccall of (((ctype, 'TY) a)) * 'TY asym * ('TY asym) list (* C function call *)
 | M_Eproc of mu_name * ('TY asym) list (* Core procedure call *)
 | M_Ewseq of 'bt mu_pattern * (('ct, 'bt, 'TY) mu_expr) * (('ct, 'bt, 'TY) mu_expr) (* weak sequencing *)
 | M_Esseq of 'bt mu_pattern * (('ct, 'bt, 'TY) mu_expr) * (('ct, 'bt, 'TY) mu_expr) (* strong sequencing *)
 | M_Ebound of int * (('ct, 'bt, 'TY) mu_expr) (* $\ldots$and boundary *)
 | M_End of (('ct, 'bt, 'TY) mu_expr) list (* nondeterministic choice *)
 | M_Erun of symbol * ('TY asym) list (* run from label *)

and ('ct, 'bt, 'TY) mu_expr = 
 | M_Expr of annot list * (('ct, 'bt, 'TY) mu_expr_)




let embed_pexpr_expr pe : ('c,'b,'a) mu_expr= 
  let (M_Pexpr (annots2, _bty, _)) = pe in
  M_Expr (annots2, (M_Epure pe))


type ('ct, 'bt, 'TY) mu_impl_decl =
  | M_Def of 'bt * ('ct, 'bt, 'TY) mu_pexpr
  | M_IFun of 'bt * (symbol * 'bt) list * ('ct, 'bt, 'TY) mu_pexpr

type ('ct, 'bt, 'TY) mu_impl = (Implementation.implementation_constant, (('ct, 'bt, 'TY) mu_impl_decl)) 
  Pmap.map

type ('lt, 'ct, 'bt, 'TY) mu_label_def = 
  | M_Return of 'lt
  | M_Label of 'lt * ((symbol * 'bt) list) * ('ct, 'bt, 'TY) mu_expr * annot list

type ('lt, 'ct, 'bt, 'TY) mu_label_defs = (symbol, (('lt, 'ct, 'bt, 'TY) mu_label_def))
  Pmap.map


type ('lt, 'ct, 'bt, 'TY) mu_fun_map_decl =
  | M_Fun of 'bt * (symbol * 'bt) list * ('ct, 'bt, 'TY) mu_pexpr
  | M_Proc of Location_ocaml.t * 'bt * (symbol * 'bt) list * ('ct, 'bt, 'TY) mu_expr * ('lt, 'ct, 'bt, 'TY) mu_label_defs
  | M_ProcDecl of Location_ocaml.t * 'bt * 'bt list
  | M_BuiltinDecl of Location_ocaml.t * 'bt * 'bt list

type ('lt, 'ct, 'bt, 'TY) mu_fun_map = (symbol, (('lt, 'ct, 'bt, 'TY) mu_fun_map_decl)) 
  Pmap.map



type mu_linking_kind = Core.linking_kind

type mu_extern_map = Core.extern_map

type ('ct, 'bt, 'TY) mu_globs =
  | M_GlobalDef of 'bt * ('ct, 'bt, 'TY) mu_expr
  | M_GlobalDecl of 'bt

type ('ct, 'bt, 'TY) mu_globs_map = (symbol, (('ct, 'bt, 'TY) mu_globs))
  Pmap.map



type 'ct mu_struct_def = (Symbol.identifier * (Annot.attributes * qualifiers * 'ct)) list *  flexible_array_member option
type 'ct mu_union_def = (Symbol.identifier * (Annot.attributes * qualifiers * 'ct)) list

type ('st_def, 'ut_def) mu_tag_definition =
  | M_StructDef of 'st_def
  | M_UnionDef of 'ut_def

type ('st,'ut) mu_tag_definitions = (Symbol.sym, ('st,'ut) mu_tag_definition)
  Pmap.map

type 'ct mu_funinfo_type = 'ct * (symbol * 'ct) list

type 'ft mu_funinfo = 
  M_funinfo of (Location_ocaml.t * Annot.attributes * 'ft * bool * bool)

type 'ft mu_funinfos = (symbol, ('ft mu_funinfo)) Pmap.map

type ('ct, 'bt, 'TY) mu_globs_list = (symbol * ('ct, 'bt, 'TY) mu_globs) list

(* a Core file is just a set of named functions *)
type ('ft, 'lt, 'ct, 'bt, 'st_def, 'ut_def, 'TY) mu_file = {
  mu_main    : symbol option;
  mu_tagDefs : ('st_def,'ut_def) mu_tag_definitions;
  mu_stdlib  : ('lt, 'ct, 'bt, 'TY) mu_fun_map;
  mu_impl    : ('ct, 'bt, 'TY) mu_impl;
  mu_globs   : ('ct, 'bt, 'TY) mu_globs_list;
  mu_funs    : ('lt, 'ct, 'bt, 'TY) mu_fun_map;
  mu_extern  : mu_extern_map;
  mu_funinfo : 'ft mu_funinfos;
  mu_loop_attributes : Annot.loop_attributes;
}


