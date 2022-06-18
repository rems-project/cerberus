open Lem_pervasives

open Ctype
open Annot
open Loc
open Mem
open Mem_common
open Core_aux

open Lem_assert_extra

module Loc = Location_ocaml
type loc = Loc.t




type trusted = 
  | Trusted of Location_ocaml.t
  | Checked


module type TYPES = sig

  type ct
  type bt

  type ift
  type ict

  type ut
  type st
  type ft
  type lt
  type gt

  type resource_predicates
  type logical_predicates

end





module Make(T : TYPES) = struct



  type symbol = Symbol.sym
  type mu_name = symbol Core.generic_name

  type 'TY act = { 
      loc: loc;
      annot: Annot.annot list;
      type_annot : 'TY;
      ct: T.ct
    }


  let act_unpack (a : 'TY act) = 
    (a.loc, a.annot, a.type_annot, a.ct)
  let act_pack loc annot type_annot ct = 
    {loc; annot; type_annot; ct}

  type 'TY acts = ('TY act) list



  type 'TY mu_object_value =  (* C object values *)
   | M_OVinteger of Impl_mem.integer_value (* integer value *)
   | M_OVfloating of Impl_mem.floating_value (* floating-point value *)
   | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
   | M_OVarray of ('TY mu_loaded_value) list (* C array value *)
   | M_OVstruct of symbol * (Symbol.identifier * T.ct * Impl_mem.mem_value) list (* C struct value *)
   | M_OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)


  and 'TY mu_loaded_value =  (* potentially unspecified C object values *)
   | M_LVspecified of 'TY mu_object_value (* non-unspecified loaded value *)

  and 'TY mu_value =  (* Core values *)
   | M_Vobject of 'TY mu_object_value (* C object value *)
   | M_Vloaded of 'TY mu_loaded_value (* loaded C object value *)
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
   | M_Cspecified (* non-unspecified loaded value *)
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
    | M_Symbol of symbol
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
   | M_PEmemberof of symbol * Symbol.identifier * 'TY mu_pexpr (* C struct/union member access *)

   | M_PEassert_undef of 'TY mu_pexpr * Location_ocaml.t * Undefined.undefined_behaviour
   | M_PEbool_to_integer of 'TY mu_pexpr
   | M_PEconv_int of 'TY act * 'TY mu_pexpr
   | M_PEconv_loaded_int of 'TY act * 'TY mu_pexpr
   | M_PEwrapI of 'TY act * 'TY mu_pexpr


  and 'TY mu_pexpr = 
   | M_Pexpr of loc * annot list * 'TY * ('TY mu_pexpr_)

  let loc_of_pexpr (M_Pexpr (loc, _, _, _)) = loc


  type 'TY mu_tpexpr_ = 
   | M_PEundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
   | M_PEerror of string * 'TY mu_pexpr (* impl-defined static error *)
   | M_PEcase of ('TY mu_pexpr) * (mu_pattern * 'TY mu_tpexpr) list (* pattern matching *)
   | M_PElet of ('TY mu_sym_or_pattern) * ('TY mu_pexpr) * ('TY mu_tpexpr) (* pure let *)
   | M_PEif of 'TY mu_pexpr * ('TY mu_tpexpr) * ('TY mu_tpexpr) (* pure if *)
   | M_PEdone of 'TY mu_pexpr

  and 'TY mu_tpexpr = 
   | M_TPexpr of loc * annot list * 'TY * ('TY mu_tpexpr_)

  let loc_of_tpexpr (M_TPexpr (loc, _, _, _)) = loc


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


  type pack_unpack =
    | Pack
    | Unpack

type have_show =
    | Have
    | Show

  type 'TY mu_expr_ =  (* (effectful) expression *)
   | M_Epure of ('TY mu_pexpr)
   | M_Ememop of 'TY mu_memop
   | M_Eaction of ('TY mu_paction) (* memory action *)
   | M_Eskip
   | M_Eccall of 'TY act * 'TY mu_pexpr * ('TY mu_pexpr) list (* C function call *)
   (* | M_Eproc of mu_name * ('TY mu_pexpr) list (\* Core procedure call *\) *)
   | M_Erpredicate of pack_unpack * Annot.to_pack_unpack * ('TY mu_pexpr) list
   | M_Elpredicate of have_show * Symbol.identifier * ('TY mu_pexpr) list
   | M_Einstantiate of Symbol.identifier option * 'TY mu_pexpr

  and 'TY mu_expr = 
   | M_Expr of loc * annot list * ('TY mu_expr_)

  let loc_of_expr (M_Expr (loc, _, _)) = loc


  type 'TY mu_texpr_ =
   | M_Elet of ('TY mu_sym_or_pattern) * ('TY mu_pexpr) * ('TY mu_texpr)
   | M_Ewseq of mu_pattern * ('TY mu_expr) * ('TY mu_texpr) (* weak sequencing *)
   | M_Esseq of ('TY mu_sym_or_pattern) * ('TY mu_expr) * ('TY mu_texpr) (* strong sequencing *)
   | M_Ecase of 'TY mu_pexpr * (mu_pattern * ('TY mu_texpr)) list (* pattern matching *)
   | M_Eif of 'TY mu_pexpr * ('TY mu_texpr) * ('TY mu_texpr)
   | M_Ebound of ('TY mu_texpr) (* $\ldots$and boundary *)
   | M_End of ('TY mu_texpr) list (* nondeterministic choice *)
   | M_Edone of 'TY mu_pexpr
   | M_Eundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
   | M_Eerror of string * 'TY mu_pexpr (* impl-defined static error *)
   | M_Erun of symbol * ('TY mu_pexpr) list (* run from label *)

  and 'TY mu_texpr = 
   | M_TExpr of loc * annot list * ('TY mu_texpr_)

  let loc_of_texpr (M_TExpr (loc, _, _)) = loc


  let embed_pexpr_expr pe : 'TY mu_expr= 
    let (M_Pexpr (loc, _, _, _)) = pe in
    M_Expr (loc, [], (M_Epure pe))


  type 'TY mu_impl_decl =
    | M_Def of T.ict * T.bt * 'TY mu_tpexpr
    | M_IFun of T.ift * T.bt * (symbol * T.bt) list * 'TY mu_tpexpr

  type 'TY mu_impl = (Implementation.implementation_constant, ('TY mu_impl_decl)) 
    Pmap.map

  type 'TY mu_label_def = 
    | M_Return of loc * T.lt
    | M_Label of loc * T.lt * ((symbol * T.bt) list) * 'TY mu_texpr * annot list

  type 'TY mu_label_defs = (symbol, ('TY mu_label_def)) Pmap.map

  let subst_label_def lt_subst substitution label_def =
    match label_def with
    | M_Return (loc, lt) -> 
       let lt = lt_subst substitution lt in
       M_Return (loc, lt)
    | M_Label (loc, lt, args, body, annots) ->
       let lt = lt_subst substitution lt in
       M_Label (loc, lt, args, body, annots)

  let subst_label_defs lt_subst substitution (label_defs : 'TY mu_label_defs) =
    Pmap.map (fun def ->
      subst_label_def lt_subst substitution def
    ) label_defs


  type 'TY mu_fun_map_decl =
    | M_Fun of T.bt * (symbol * T.bt) list * 'TY mu_tpexpr
    | M_Proc of Location_ocaml.t * T.bt * (symbol * T.bt) list * 'TY mu_texpr * 'TY mu_label_defs
    | M_ProcDecl of Location_ocaml.t * T.bt * T.bt list
    | M_BuiltinDecl of Location_ocaml.t * T.bt * T.bt list

  type 'TY mu_fun_map = (symbol, ('TY mu_fun_map_decl)) 
    Pmap.map



  type mu_linking_kind = Core.linking_kind

  type mu_extern_map = Core.extern_map

  type 'TY mu_globs =
    | M_GlobalDef of symbol * (T.bt * T.gt) * 'TY mu_texpr
    | M_GlobalDecl of symbol * (T.bt * T.gt)

  type 'TY mu_globs_map = (symbol, 'TY mu_globs)
    Pmap.map



  type mu_tag_definition =
    | M_StructDef of T.st
    | M_UnionDef of T.ut

  type mu_tag_definitions = (Symbol.sym, mu_tag_definition)
    Pmap.map

  type mu_funinfo = 
    M_funinfo of Location_ocaml.t * Annot.attributes * T.ft * trusted * bool

  type mu_funinfos = 
    (symbol, mu_funinfo) Pmap.map

  type 'TY mu_globs_list = (symbol * 'TY mu_globs) list

  (* a Core file is just a set of named functions *)
  type 'TY mu_file = {
    mu_main    : symbol option;
    mu_tagDefs : mu_tag_definitions;
    mu_stdlib  : 'TY mu_fun_map;
    mu_impl    : 'TY mu_impl;
    mu_globs   : 'TY mu_globs_list;
    mu_funs    : 'TY mu_fun_map;
    mu_extern  : mu_extern_map;
    mu_funinfo :  mu_funinfos;
    mu_loop_attributes : Annot.loop_attributes;
    mu_resource_predicates : T.resource_predicates;
    mu_logical_predicates : T.logical_predicates;
  }


end







module SimpleTypes : TYPES
       with type ct = Ctype.ctype
       with type bt = Core.core_base_type
       with type ift = Core.core_base_type * (Core.core_base_type) list
       with type ict = Core.core_base_type
       with type ut = (Symbol.identifier * (Annot.attributes * qualifiers * Ctype.ctype)) list
       with type st = (Symbol.identifier * (Annot.attributes * qualifiers * Ctype.ctype)) list *  flexible_array_member option
       with type ft = Ctype.ctype * (Symbol.sym * Ctype.ctype) list * bool
       with type lt = (Symbol.sym option * (Ctype.ctype * bool)) list
       with type gt = Ctype.ctype
       with type resource_predicates = unit
       with type logical_predicates = unit
  = 
struct

  type ct = Ctype.ctype
  type bt = Core.core_base_type
  type ift = bt * bt list
  type ict = bt

  type ut = (Symbol.identifier * (Annot.attributes * qualifiers * ct)) list
  type st = (Symbol.identifier * (Annot.attributes * qualifiers * ct)) list *  flexible_array_member option
  type ft = ct * (Symbol.sym * ct) list * bool
  type lt = (Symbol.sym option * (Ctype.ctype * bool)) list
  type gt = ct
  type resource_predicates = unit
  type logical_predicates = unit

end
