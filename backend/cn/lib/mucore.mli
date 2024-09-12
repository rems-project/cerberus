(* Module Mucore - CN-specific variant of Cerberus Core

   A more specialized version of Core – this is what CN actually uses. (Among a few other
   differences, Core can pass around C types as values – CN is more restrictive, for
   simplicity.) *)

(* TODO: BCP: Not actually clear to me that this module needs a signature -- it's
   enormous, but mostly types and small functions, and everything it defines is used
   elsewhere. *)

type trusted =
  | Trusted of Locations.t
  | Checked

type make_logical_function = Make_Logical_Function of Id.t

module T : sig
  type ct = Sctypes.t

  type bt = BaseTypes.t

  type cbt = Cerb_frontend.Core.core_base_type

  type ft = ArgumentTypes.ft

  type lt = ArgumentTypes.lt

  type rt = ReturnTypes.t

  type st = Memory.struct_layout

  type ut = unit

  type logical_arguments = Sym.t * (Sym.t * BaseTypes.t) list

  type resource_predicates = (Sym.t * ResourcePredicates.definition) list

  type logical_predicates = (Sym.t * LogicalFunctions.definition) list
end

type symbol = Cerb_frontend.Symbol.sym

(** Annotated C type.  The annotations are typically an explanation of
    something that might go wrong (e.g., overflow on an integer type). *)
type act =
  { loc : Locations.t; (** Source location *)
    annot : Cerb_frontend.Annot.annot list; (** Annotations *)
    ct : T.ct (** Affected type *)
  }

type 'TY mu_object_value_ =
  | M_OVinteger of Cerb_frontend.Impl_mem.integer_value
  | M_OVfloating of Cerb_frontend.Impl_mem.floating_value
  | M_OVpointer of Cerb_frontend.Impl_mem.pointer_value
  | M_OVarray of 'TY mu_object_value list
  | M_OVstruct of
      symbol
      * (Cerb_frontend.Symbol.identifier * T.ct * Cerb_frontend.Impl_mem.mem_value) list
  | M_OVunion of
      symbol * Cerb_frontend.Symbol.identifier * Cerb_frontend.Impl_mem.mem_value

and 'TY mu_object_value = M_OV of 'TY * 'TY mu_object_value_

and 'TY mu_value_ =
  | M_Vobject of 'TY mu_object_value
  | M_Vctype of Cerb_frontend.Ctype.ctype
  | M_Vfunction_addr of Cerb_frontend.Symbol.sym
  | M_Vunit
  | M_Vtrue
  | M_Vfalse
  | M_Vlist of T.cbt * 'TY mu_value list
  | M_Vtuple of 'TY mu_value list

and 'TY mu_value = M_V of 'TY * 'TY mu_value_

type mu_ctor =
  | M_Cnil of T.cbt
  | M_Ccons
  | M_Ctuple
  | M_Carray

type 'TY mu_pattern_ =
  | M_CaseBase of (Cerb_frontend.Symbol.sym option * T.cbt)
  | M_CaseCtor of mu_ctor * 'TY mu_pattern list

and 'TY mu_pattern =
  | M_Pattern of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY mu_pattern_

type mu_function =
  | M_F_params_length
  | M_F_params_nth
  | M_F_are_compatible
  | M_F_size_of
  | M_F_align_of
  | M_F_max_int
  | M_F_min_int
  | M_F_ctype_width

type bw_binop =
  | M_BW_OR
  | M_BW_AND
  | M_BW_XOR

type bw_unop =
  | M_BW_COMPL
  | M_BW_CTZ
  | M_BW_FFS

(** What to do on out of bounds.
    The annotated C type is the result type of the operation. *)
type bound_kind =
  | M_Bound_Wrap of act (** Wrap around (used for unsigned types) *)
  | M_Bound_Except of act (** Report an exception, for signed types *)

val bound_kind_act : bound_kind -> act

type 'TY mu_pexpr_ =
  | M_PEsym of symbol
  | M_PEval of 'TY mu_value
  | M_PEconstrained of (Cerb_frontend.Mem.mem_iv_constraint * 'TY mu_pexpr) list
  | M_PEctor of mu_ctor * 'TY mu_pexpr list
  | M_PEbitwise_unop of bw_unop * 'TY mu_pexpr
  | M_PEbitwise_binop of bw_binop * 'TY mu_pexpr * 'TY mu_pexpr
  | M_Cfvfromint of 'TY mu_pexpr
  | M_Civfromfloat of act * 'TY mu_pexpr
  | M_PEarray_shift of 'TY mu_pexpr * T.ct * 'TY mu_pexpr
  | M_PEmember_shift of 'TY mu_pexpr * symbol * Cerb_frontend.Symbol.identifier
  | M_PEnot of 'TY mu_pexpr
  | M_PEop of Cerb_frontend.Core.binop * 'TY mu_pexpr * 'TY mu_pexpr
  | M_PEapply_fun of mu_function * 'TY mu_pexpr list
  | M_PEstruct of symbol * (Cerb_frontend.Symbol.identifier * 'TY mu_pexpr) list
  | M_PEunion of symbol * Cerb_frontend.Symbol.identifier * 'TY mu_pexpr
  | M_PEcfunction of 'TY mu_pexpr
  | M_PEmemberof of symbol * Cerb_frontend.Symbol.identifier * 'TY mu_pexpr
  | M_PEbool_to_integer of 'TY mu_pexpr
  | M_PEconv_int of 'TY mu_pexpr * 'TY mu_pexpr
  | M_PEconv_loaded_int of 'TY mu_pexpr * 'TY mu_pexpr
  | M_PEwrapI of act * 'TY mu_pexpr
  | M_PEcatch_exceptional_condition of act * 'TY mu_pexpr
  | M_PEbounded_binop of bound_kind * Cerb_frontend.Core.iop * 'TY mu_pexpr * 'TY mu_pexpr
  | M_PEis_representable_integer of 'TY mu_pexpr * act
  | M_PEundef of Cerb_location.t * Cerb_frontend.Undefined.undefined_behaviour
  | M_PEerror of string * 'TY mu_pexpr
  | M_PElet of 'TY mu_pattern * 'TY mu_pexpr * 'TY mu_pexpr
  | M_PEif of 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr

and 'TY mu_pexpr =
  | M_Pexpr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY mu_pexpr_

val loc_of_pexpr : 'a mu_pexpr -> Locations.t

type m_kill_kind =
  | M_Dynamic
  | M_Static of T.ct

type 'TY mu_action_ =
  | M_Create of 'TY mu_pexpr * act * Cerb_frontend.Symbol.prefix
  | M_CreateReadOnly of 'TY mu_pexpr * act * 'TY mu_pexpr * Cerb_frontend.Symbol.prefix
  | M_Alloc of 'TY mu_pexpr * 'TY mu_pexpr * Cerb_frontend.Symbol.prefix
  | M_Kill of m_kill_kind * 'TY mu_pexpr
  | M_Store of
      bool * act * 'TY mu_pexpr * 'TY mu_pexpr * Cerb_frontend.Cmm_csem.memory_order
  | M_Load of act * 'TY mu_pexpr * Cerb_frontend.Cmm_csem.memory_order
  | M_RMW of
      act
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | M_Fence of Cerb_frontend.Cmm_csem.memory_order
  | M_CompareExchangeStrong of
      act
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | M_CompareExchangeWeak of
      act
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * 'TY mu_pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | M_LinuxFence of Cerb_frontend.Linux.linux_memory_order
  | M_LinuxLoad of act * 'TY mu_pexpr * Cerb_frontend.Linux.linux_memory_order
  | M_LinuxStore of
      act * 'TY mu_pexpr * 'TY mu_pexpr * Cerb_frontend.Linux.linux_memory_order
  | M_LinuxRMW of
      act * 'TY mu_pexpr * 'TY mu_pexpr * Cerb_frontend.Linux.linux_memory_order

type 'TY mu_action = M_Action of Cerb_location.t * 'TY mu_action_

type 'TY mu_paction = M_Paction of Cerb_frontend.Core.polarity * 'TY mu_action

type 'TY mu_memop =
  | M_PtrEq of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrNe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Ptrdiff of (act * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_IntFromPtr of (act * act * 'TY mu_pexpr)
  | M_PtrFromInt of (act * act * 'TY mu_pexpr)
  | M_PtrValidForDeref of (act * 'TY mu_pexpr)
  | M_PtrWellAligned of (act * 'TY mu_pexpr)
  | M_PtrArrayShift of ('TY mu_pexpr * act * 'TY mu_pexpr)
  | M_PtrMemberShift of (symbol * Cerb_frontend.Symbol.identifier * 'TY mu_pexpr)
  | M_Memcpy of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Memcmp of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Realloc of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_start of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_copy of 'TY mu_pexpr
  | M_Va_arg of ('TY mu_pexpr * act)
  | M_Va_end of 'TY mu_pexpr
  | M_CopyAllocId of ('TY mu_pexpr * 'TY mu_pexpr)

type 'TY mu_expr_ =
  | M_Epure of 'TY mu_pexpr
  | M_Ememop of 'TY mu_memop
  | M_Eaction of 'TY mu_paction
  | M_Eskip
  | M_Eccall of act * 'TY mu_pexpr * 'TY mu_pexpr list
  | M_Elet of 'TY mu_pattern * 'TY mu_pexpr * 'TY mu_expr
  | M_Eunseq of 'TY mu_expr list
  | M_Ewseq of 'TY mu_pattern * 'TY mu_expr * 'TY mu_expr
  | M_Esseq of 'TY mu_pattern * 'TY mu_expr * 'TY mu_expr
  | M_Eif of 'TY mu_pexpr * 'TY mu_expr * 'TY mu_expr
  | M_Ebound of 'TY mu_expr
  | M_End of 'TY mu_expr list
  | M_Erun of symbol * 'TY mu_pexpr list
  | M_CN_progs of
      (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement list
      * Cnprog.cn_prog list

and 'TY mu_expr =
  | M_Expr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY mu_expr_

val loc_of_expr : 'a mu_expr -> Locations.t

type info = Locations.info

type 'i mu_arguments_l =
  | M_Define of (Sym.t * IndexTerms.t) * info * 'i mu_arguments_l
  | M_Resource of (Sym.t * (ResourceTypes.t * BaseTypes.t)) * info * 'i mu_arguments_l
  | M_Constraint of LogicalConstraints.t * info * 'i mu_arguments_l
  | M_I of 'i

val dtree_of_mu_arguments_l
  :  ('a -> Cerb_frontend.Pp_ast.doc_tree) ->
  'a mu_arguments_l ->
  Cerb_frontend.Pp_ast.doc_tree

type 'i mu_arguments =
  | M_Computational of (Sym.t * T.bt) * info * 'i mu_arguments
  | M_L of 'i mu_arguments_l

val dtree_of_mu_arguments
  :  ('a -> Cerb_frontend.Pp_ast.doc_tree) ->
  'a mu_arguments ->
  Cerb_frontend.Pp_ast.doc_tree

val mu_count_computational : 'a mu_arguments -> int

val mDefine : (Sym.t * IndexTerms.t) * info -> 'a mu_arguments_l -> 'a mu_arguments_l

val mResource
  :  (Sym.t * (ResourceTypes.t * BaseTypes.t)) * info ->
  'a mu_arguments_l ->
  'a mu_arguments_l

val mConstraint : LogicalConstraints.t * info -> 'a mu_arguments_l -> 'a mu_arguments_l

val mComputational : (Sym.t * T.bt) * info -> 'a mu_arguments -> 'a mu_arguments

val mConstraints
  :  (LogicalConstraints.t * info) list ->
  'a mu_arguments_l ->
  'a mu_arguments_l

val mResources
  :  ((Sym.t * (ResourceTypes.t * BaseTypes.t)) * info) list ->
  'a mu_arguments_l ->
  'a mu_arguments_l

val mu_fun_param_types : mu_function -> BaseTypes.t list

val is_ctype_const : 'a mu_pexpr -> Cerb_frontend.Ctype.ctype option

val mu_fun_return_type
  :  mu_function ->
  'a mu_pexpr list ->
  [> `Returns_BT of BaseTypes.t | `Returns_Integer ] Option.t

val pp_function : mu_function -> Pp.document

val is_undef_or_error_pexpr : 'a mu_pexpr -> bool

val is_undef_or_error_expr : 'a mu_expr -> bool

val bt_of_value : 'a mu_value -> 'a

val bt_of_object_value : 'a mu_object_value -> 'a

val bt_of_pattern : 'a mu_pattern -> 'a

val loc_of_pattern : 'a mu_pattern -> Locations.t

val bt_of_expr : 'TY mu_expr -> 'TY

val bt_of_pexpr : 'TY mu_pexpr -> 'TY

val evaluate_fun
  :  mu_function ->
  IndexTerms.t list ->
  [> `Result_IT of IndexTerms.t | `Result_Integer of Z.t ] Option.m

type parse_ast_label_spec =
  { label_spec : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list }

type 'TY mu_label_def =
  | M_Return of Locations.t
  | M_Label of
      Locations.t
      * 'TY mu_expr mu_arguments
      * Cerb_frontend.Annot.annot list
      * parse_ast_label_spec

val dtree_of_label_def : 'a mu_label_def -> Cerb_frontend.Pp_ast.doc_tree

type 'TY mu_label_defs = (symbol, 'TY mu_label_def) Pmap.map

type 'TY mu_proc_args_and_body = ('TY mu_expr * 'TY mu_label_defs * T.rt) mu_arguments

type parse_ast_function_specification =
  { accesses : (Sym.t * Cerb_frontend.Ctype.ctype) list;
    requires : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list;
    ensures : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list
  }

type 'TY mu_fun_map_decl =
  | M_Proc of
      Cerb_location.t
      * 'TY mu_proc_args_and_body
      * trusted
      * parse_ast_function_specification
  | M_ProcDecl of Cerb_location.t * T.ft option

type 'TY mu_fun_map = (symbol, 'TY mu_fun_map_decl) Pmap.map

type mu_extern_map = Cerb_frontend.Core.extern_map

type 'TY mu_globs =
  | M_GlobalDef of T.ct * 'TY mu_expr
  | M_GlobalDecl of T.ct

type 'TY mu_globs_map = (symbol, 'TY mu_globs) Pmap.map

type mu_tag_definition =
  | M_StructDef of T.st
  | M_UnionDef of T.ut

type mu_tag_definitions = (Cerb_frontend.Symbol.sym, mu_tag_definition) Pmap.map

type 'TY mu_globs_list = (symbol * 'TY mu_globs) list

type mu_datatype =
  { loc : Locations.t;
    cases : (Sym.t * (Id.t * T.bt) list) list
  }

type mu_function_to_convert =
  { loc : Locations.t;
    c_fun_sym : Sym.t;
    l_fun_sym : Sym.t
  }

type 'TY mu_file =
  { mu_main : symbol option;
    mu_tagDefs : mu_tag_definitions;
    mu_globs : 'TY mu_globs_list;
    mu_funs : 'TY mu_fun_map;
    mu_extern : mu_extern_map;
    mu_stdlib_syms : Set.Make(Sym).t;
    mu_mk_functions : mu_function_to_convert list;
    mu_resource_predicates : T.resource_predicates;
    mu_logical_predicates : T.logical_predicates;
    mu_datatypes : (Sym.t * mu_datatype) list;
    mu_lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
    mu_call_funinfo : (symbol, Sctypes.c_concrete_sig) Pmap.map
  }
