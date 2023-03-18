module CF=Cerb_frontend
open Cerb_frontend
open Annot

module Loc = Location_ocaml
type loc = Loc.t




type trusted = 
  | Trusted of Location_ocaml.t
  | Checked

type make_logical_function =
  | Make_Logical_Function of Id.t



module T = struct
  type ct = Sctypes.t
  type bt = BaseTypes.t
  type ft = ArgumentTypes.ft
  type lt = ArgumentTypes.lt
  type rt = ReturnTypes.t
  type st = Memory.struct_layout
  type ut = unit
  (* type mapping = Mapping.t *)
  type logical_arguments = (Sym.t * (Sym.t * BaseTypes.t) list)
  type resource_predicates = (Sym.t * ResourcePredicates.definition) list
  type logical_predicates = (Sym.t * LogicalPredicates.definition) list
end



type symbol = Symbol.sym

type 'TY act = { 
    loc: loc;
    annot: Annot.annot list;
    type_annot : 'TY;
    ct: T.ct
  }





type 'TY mu_object_value =  (* C object values *)
 | M_OVinteger of Impl_mem.integer_value (* integer value *)
 | M_OVfloating of Impl_mem.floating_value (* floating-point value *)
 | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
 | M_OVarray of ('TY mu_object_value) list (* C array value *)
 | M_OVstruct of symbol * (Symbol.identifier * T.ct * Impl_mem.mem_value) list (* C struct value *)
 | M_OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)


(* and 'TY mu_loaded_value =  (\* potentially unspecified C object values *\) *)
(*  | M_LVspecified of 'TY mu_object_value (\* non-unspecified loaded value *\) *)

and 'TY mu_value =  (* Core values *)
 | M_Vobject of 'TY mu_object_value (* C object value *)
 (* | M_Vloaded of 'TY mu_loaded_value (\* loaded C object value *\) *)
 | M_Vunit
 | M_Vtrue
 | M_Vfalse
 | M_Vlist of T.bt * ('TY mu_value) list
 | M_Vtuple of ('TY mu_value) list (* tuple *)



type mu_ctor =  (* data constructors *)
 | M_Cnil of T.bt (* empty list *) 
 (* annotated with the type of the list items *)
 | M_Ccons (* list cons *)
 | M_Ctuple (* tuple *)
 | M_Carray (* C array *)
 (* | M_Cspecified (\* non-unspecified loaded value *\) *)
 (* | M_CivCOMPL (\* bitwise complement *\)
  * | M_CivAND (\* bitwise AND *\)
  * | M_CivOR (\* bitwise OR *\)
  * | M_CivXOR (\* bitwise XOR *\)
  * | M_Cfvfromint (\* cast integer to floating value *\)
  * | M_Civfromfloat (\* cast floating to integer value *\) *)

type mu_pattern_ = 
 | M_CaseBase of (Symbol.sym option * T.bt)
 | M_CaseCtor of mu_ctor * mu_pattern list

and mu_pattern = 
 | M_Pattern of loc * annot list * mu_pattern_

type 'TY mu_sym_or_pattern = 
  (* | M_Symbol of symbol *)
  | M_Pat of mu_pattern

type 'TY mu_pexpr_ =  (* Core pure expressions *)
 | M_PEsym of symbol
 (* | M_PEimpl of Implementation.implementation_constant (\* implementation-defined constant *\) *)
 | M_PEval of 'TY mu_value
 | M_PEconstrained of (Mem.mem_iv_constraint * 'TY mu_pexpr) list (* constrained value *)
 | M_PEctor of mu_ctor * ('TY mu_pexpr) list (* data constructor application *)
 | M_CivCOMPL of 'TY act * 'TY mu_pexpr (* bitwise complement *)
 | M_CivAND of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr (* bitwise AND *)
 | M_CivOR of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr (* bitwise OR *)
 | M_CivXOR of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr (* bitwise XOR *)
 | M_Cfvfromint of 'TY mu_pexpr (* cast integer to floating value *)
 | M_Civfromfloat of 'TY act * 'TY mu_pexpr (* cast floating to integer value *)
 | M_PEarray_shift of ('TY mu_pexpr) * T.ct * ('TY mu_pexpr) (* pointer array shift *)
 | M_PEmember_shift of ('TY mu_pexpr) * symbol * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'TY mu_pexpr (* boolean not *)
 | M_PEop of Core.binop * ('TY mu_pexpr) * ('TY mu_pexpr)
 | M_PEstruct of symbol * (Symbol.identifier * 'TY mu_pexpr) list (* C struct expression *)
 | M_PEunion of symbol * Symbol.identifier * 'TY mu_pexpr (* C union expression *)
 | M_PEcfunction of 'TY mu_pexpr
 | M_PEmemberof of symbol * Symbol.identifier * 'TY mu_pexpr (* C struct/union member access *)

 (* | M_PEassert_undef of 'TY mu_pexpr * Location_ocaml.t * Undefined.undefined_behaviour *)
 | M_PEbool_to_integer of 'TY mu_pexpr
 | M_PEconv_int of 'TY act * 'TY mu_pexpr
 | M_PEconv_loaded_int of 'TY act * 'TY mu_pexpr
 | M_PEwrapI of 'TY act * 'TY mu_pexpr
 | M_PEcatch_exceptional_condition of 'TY act * 'TY mu_pexpr
 | M_PEis_representable_integer of 'TY mu_pexpr * 'TY act

 | M_PEundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_PEerror of string * 'TY mu_pexpr (* impl-defined static error *)
 (* | M_PEcase of ('TY mu_pexpr) * (mu_pattern * 'TY mu_tpexpr) list (\* pattern matching *\) *)
 | M_PElet of ('TY mu_sym_or_pattern) * ('TY mu_pexpr) * ('TY mu_pexpr) (* pure let *)
 | M_PEif of 'TY mu_pexpr * ('TY mu_pexpr) * ('TY mu_pexpr) (* pure if *)



and 'TY mu_pexpr = 
 | M_Pexpr of loc * annot list * 'TY * ('TY mu_pexpr_)

let loc_of_pexpr (M_Pexpr (loc, _, _, _)) = loc



type m_kill_kind = 
  | M_Dynamic
  | M_Static of T.ct

type 'TY mu_action_ =  (* memory actions *)
 | M_Create of 'TY mu_pexpr * ('TY act) * Symbol.prefix
 | M_CreateReadOnly of 'TY mu_pexpr * 'TY act * 'TY mu_pexpr * Symbol.prefix
 | M_Alloc of 'TY mu_pexpr * 'TY mu_pexpr * Symbol.prefix
 | M_Kill of m_kill_kind * 'TY mu_pexpr (* the boolean indicates whether the action is dynamic (i.e. free()) *)
 | M_Store of bool * 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
 | M_Load of 'TY act * 'TY mu_pexpr * Cmm_csem.memory_order
 | M_RMW of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of 'TY act * 'TY mu_pexpr * Linux.linux_memory_order
 | M_LinuxStore of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Linux.linux_memory_order
 | M_LinuxRMW of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Linux.linux_memory_order


type 'TY mu_action = 
 | M_Action of Location_ocaml.t * ('TY mu_action_)


type 'TY mu_paction =  (* memory actions with Core.polarity *)
 | M_Paction of Core.polarity * ('TY mu_action)

type 'TY mu_memop =
  | M_PtrEq of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrNe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Ptrdiff of ('TY act * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_IntFromPtr of ('TY act * 'TY act * 'TY mu_pexpr)
  | M_PtrFromInt of ('TY act * 'TY act * 'TY mu_pexpr)
  | M_PtrValidForDeref of ('TY act * 'TY mu_pexpr)
  | M_PtrWellAligned of ('TY act * 'TY mu_pexpr)
  | M_PtrArrayShift of ('TY mu_pexpr * 'TY act * 'TY mu_pexpr)
  | M_Memcpy of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Memcmp of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Realloc of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_start  of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_copy of ('TY mu_pexpr)
  | M_Va_arg of ('TY mu_pexpr * 'TY act)
  | M_Va_end of ('TY mu_pexpr)









type 'TY mu_expr_ =  (* (effectful) expression *)
 | M_Epure of ('TY mu_pexpr)
 | M_Ememop of 'TY mu_memop
 | M_Eaction of ('TY mu_paction) (* memory action *)
 | M_Eskip
 | M_Eccall of 'TY act * 'TY mu_pexpr * ('TY mu_pexpr) list (* C function call *)
 (* | M_Eproc of mu_name * ('TY mu_pexpr) list (\* Core procedure call *\) *)

 | M_Elet of ('TY mu_sym_or_pattern) * ('TY mu_pexpr) * ('TY mu_expr)
 | M_Eunseq of ('TY mu_expr) list (* unsequenced expressions *)
 | M_Ewseq of mu_pattern * ('TY mu_expr) * ('TY mu_expr) (* weak sequencing *)
 | M_Esseq of mu_pattern * ('TY mu_expr) * ('TY mu_expr) (* strong sequencing *)
 (* | M_Ecase of 'TY mu_pexpr * (mu_pattern * ('TY mu_texpr)) list (\* pattern matching *\) *)
 | M_Eif of 'TY mu_pexpr * ('TY mu_expr) * ('TY mu_expr)
 | M_Ebound of ('TY mu_expr) (* $\ldots$and boundary *)
 | M_End of ('TY mu_expr) list (* nondeterministic choice *)
 (* | M_Edone of 'TY mu_expr *)
 | M_Erun of symbol * ('TY mu_pexpr) list (* run from label *)

 | M_CN_progs of Cnprog.cn_prog list


and 'TY mu_expr = 
 | M_Expr of loc * annot list * ('TY mu_expr_)

let loc_of_expr (M_Expr (loc, _, _)) = loc



let embed_pexpr_expr pe : 'TY mu_expr= 
  let (M_Pexpr (loc, _, _, _)) = pe in
  M_Expr (loc, [], (M_Epure pe))


type info = Locations.info

type 'i mu_arguments_l = 
  | M_Define of (Sym.t * IndexTerms.t) * info * 'i mu_arguments_l
  | M_Resource of (Sym.t * (ResourceTypes.t * BaseTypes.t)) * info * 'i mu_arguments_l
  | M_Constraint of LogicalConstraints.t * info * 'i mu_arguments_l
  | M_I of 'i

type 'i mu_arguments = 
  | M_Computational of (Sym.t * T.bt) * info * 'i mu_arguments
  | M_L of 'i mu_arguments_l


let rec mu_count_computational = function
  | M_Computational (_, _, args) -> mu_count_computational args + 1
  | M_L _ -> 0

let mDefine (bound, info) t = M_Define (bound, info, t)
let mResource (bound, info) t = M_Resource (bound, info, t)
let mConstraint (lc, info) t = M_Constraint (lc, info, t)
let mComputational (bound, info) t = M_Computational (bound, info, t)

let mConstraints lcs t = List.fold_right mConstraint lcs t
let mResources res t = List.fold_right mResource res t



type 'TY mu_label_def = 
  | M_Return of loc
  | M_Label of loc * ('TY mu_expr) mu_arguments * annot list

type 'TY mu_label_defs = 
  (symbol, ('TY mu_label_def)) Pmap.map



type 'TY mu_proc_args_and_body =
  ('TY mu_expr * 'TY mu_label_defs * T.rt) mu_arguments


type 'TY mu_fun_map_decl =
  (* | M_Fun of T.bt * (symbol * T.bt) list * 'TY mu_pexpr *)
  | M_Proc of Location_ocaml.t * 'TY mu_proc_args_and_body * trusted
  | M_ProcDecl of Location_ocaml.t * T.ft
  (* | M_BuiltinDecl of Location_ocaml.t * T.bt * T.bt list *)

type 'TY mu_fun_map = 
  (symbol, 'TY mu_fun_map_decl) Pmap.map



type mu_extern_map = Core.extern_map

type 'TY mu_globs =
  | M_GlobalDef of (T.bt * T.ct) * 'TY mu_expr
  | M_GlobalDecl of (T.bt * T.ct)

type 'TY mu_globs_map = 
  (symbol, 'TY mu_globs) Pmap.map


type mu_tag_definition =
  | M_StructDef of T.st
  | M_UnionDef of T.ut

type mu_tag_definitions = 
  (Symbol.sym, mu_tag_definition) Pmap.map

type 'TY mu_globs_list = 
  (symbol * 'TY mu_globs) list


type 'TY mu_file = {
  mu_main    : symbol option;
  mu_tagDefs : mu_tag_definitions;
  mu_globs   : 'TY mu_globs_list;
  mu_funs    : 'TY mu_fun_map;
  mu_extern  : mu_extern_map;
  mu_resource_predicates : T.resource_predicates;
  mu_logical_predicates : T.logical_predicates;
  mu_datatypes : (Sym.t * BaseTypes.datatype_info) list;
  mu_constructors : (Sym.t * BaseTypes.constr_info) list;
  mu_lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
}






