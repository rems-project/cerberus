(* Module Mucore - CN-specific variant of Cerberus Core

   A more specialized version of Core – this is what CN actually uses. (Among a few other
   differences, Core can pass around C types as values – CN is more restrictive, for
   simplicity.) *)

(** Annotated C type.  The annotations are typically an explanation of
    something that might go wrong (e.g., overflow on an integer type). *)
type act =
  { loc : Locations.t; (** Source location *)
    annot : Cerb_frontend.Annot.annot list; (** Annotations *)
    ct : Sctypes.t (** Affected type *)
  }

type 'TY object_value_ =
  | OVinteger of Cerb_frontend.Impl_mem.integer_value
  | OVfloating of Cerb_frontend.Impl_mem.floating_value
  | OVpointer of Cerb_frontend.Impl_mem.pointer_value
  | OVarray of 'TY object_value list
  | OVstruct of Sym.t * (Id.t * Sctypes.t * Cerb_frontend.Impl_mem.mem_value) list
  | OVunion of Sym.t * Id.t * Cerb_frontend.Impl_mem.mem_value

and 'TY object_value = OV of 'TY * 'TY object_value_

and 'TY value_ =
  | Vobject of 'TY object_value
  | Vctype of Cerb_frontend.Ctype.ctype
  | Vfunction_addr of Sym.t
  | Vunit
  | Vtrue
  | Vfalse
  | Vlist of Cerb_frontend.Core.core_base_type * 'TY value list
  | Vtuple of 'TY value list

and 'TY value = V of 'TY * 'TY value_

val bt_of_value : 'a value -> 'a

val bt_of_object_value : 'a object_value -> 'a

type ctor =
  | Cnil of Cerb_frontend.Core.core_base_type
  | Ccons
  | Ctuple
  | Carray

type 'TY pattern_ =
  | CaseBase of (Sym.t option * Cerb_frontend.Core.core_base_type)
  | CaseCtor of ctor * 'TY pattern list

and 'TY pattern =
  | Pattern of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY pattern_

val bt_of_pattern : 'a pattern -> 'a

val loc_of_pattern : 'a pattern -> Locations.t

type mu_function =
  | F_params_length
  | F_params_nth
  | F_are_compatible
  | F_size_of
  | F_align_of
  | F_max_int
  | F_min_int
  | F_ctype_width

val pp_function : mu_function -> Pp.document

val fun_param_types : mu_function -> BaseTypes.t list

val evaluate_fun
  :  mu_function ->
  IndexTerms.t list ->
  [> `Result_IT of IndexTerms.t | `Result_Integer of Z.t ] Option.m

type bw_binop =
  | BW_OR
  | BW_AND
  | BW_XOR

type bw_unop =
  | BW_COMPL
  | BW_CTZ
  | BW_FFS

(** What to do on out of bounds.
    The annotated C type is the result type of the operation. *)
type bound_kind =
  | Bound_Wrap of act (** Wrap around (used for unsigned types) *)
  | Bound_Except of act (** Report an exception, for signed types *)

val bound_kind_act : bound_kind -> act

type 'TY pexpr_ =
  | PEsym of Sym.t
  | PEval of 'TY value
  | PEconstrained of (Cerb_frontend.Mem.mem_iv_constraint * 'TY pexpr) list
  | PEctor of ctor * 'TY pexpr list
  | PEbitwise_unop of bw_unop * 'TY pexpr
  | PEbitwise_binop of bw_binop * 'TY pexpr * 'TY pexpr
  | Cfvfromint of 'TY pexpr
  | Civfromfloat of act * 'TY pexpr
  | PEarray_shift of 'TY pexpr * Sctypes.t * 'TY pexpr
  | PEmember_shift of 'TY pexpr * Sym.t * Id.t
  | PEnot of 'TY pexpr
  | PEop of Cerb_frontend.Core.binop * 'TY pexpr * 'TY pexpr
  | PEapply_fun of mu_function * 'TY pexpr list
  | PEstruct of Sym.t * (Id.t * 'TY pexpr) list
  | PEunion of Sym.t * Id.t * 'TY pexpr
  | PEcfunction of 'TY pexpr
  | PEmemberof of Sym.t * Id.t * 'TY pexpr
  | PEbool_to_integer of 'TY pexpr
  | PEconv_int of 'TY pexpr * 'TY pexpr
  | PEconv_loaded_int of 'TY pexpr * 'TY pexpr
  | PEwrapI of act * 'TY pexpr
  | PEcatch_exceptional_condition of act * 'TY pexpr
  | PEbounded_binop of bound_kind * Cerb_frontend.Core.iop * 'TY pexpr * 'TY pexpr
  | PEis_representable_integer of 'TY pexpr * act
  | PEundef of Locations.t * Cerb_frontend.Undefined.undefined_behaviour
  | PEerror of string * 'TY pexpr
  | PElet of 'TY pattern * 'TY pexpr * 'TY pexpr
  | PEif of 'TY pexpr * 'TY pexpr * 'TY pexpr

and 'TY pexpr = Pexpr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY pexpr_

val loc_of_pexpr : 'a pexpr -> Locations.t

val bt_of_pexpr : 'TY pexpr -> 'TY

val is_undef_or_error_pexpr : 'a pexpr -> bool

val fun_return_type
  :  mu_function ->
  'a pexpr list ->
  [> `Returns_BT of BaseTypes.t | `Returns_Integer ] Option.t

type m_kill_kind =
  | Dynamic
  | Static of Sctypes.t

type 'TY action_ =
  | Create of 'TY pexpr * act * Cerb_frontend.Symbol.prefix
  | CreateReadOnly of 'TY pexpr * act * 'TY pexpr * Cerb_frontend.Symbol.prefix
  | Alloc of 'TY pexpr * 'TY pexpr * Cerb_frontend.Symbol.prefix
  | Kill of m_kill_kind * 'TY pexpr
  | Store of bool * act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Cmm_csem.memory_order
  | Load of act * 'TY pexpr * Cerb_frontend.Cmm_csem.memory_order
  | RMW of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | Fence of Cerb_frontend.Cmm_csem.memory_order
  | CompareExchangeStrong of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | CompareExchangeWeak of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | LinuxFence of Cerb_frontend.Linux.linux_memory_order
  | LinuxLoad of act * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order
  | LinuxStore of act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order
  | LinuxRMW of act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order

type 'TY action = Action of Locations.t * 'TY action_

type 'TY paction = Paction of Cerb_frontend.Core.polarity * 'TY action

type 'TY memop =
  | PtrEq of ('TY pexpr * 'TY pexpr)
  | PtrNe of ('TY pexpr * 'TY pexpr)
  | PtrLt of ('TY pexpr * 'TY pexpr)
  | PtrGt of ('TY pexpr * 'TY pexpr)
  | PtrLe of ('TY pexpr * 'TY pexpr)
  | PtrGe of ('TY pexpr * 'TY pexpr)
  | Ptrdiff of (act * 'TY pexpr * 'TY pexpr)
  | IntFromPtr of (act * act * 'TY pexpr)
  | PtrFromInt of (act * act * 'TY pexpr)
  | PtrValidForDeref of (act * 'TY pexpr)
  | PtrWellAligned of (act * 'TY pexpr)
  | PtrArrayShift of ('TY pexpr * act * 'TY pexpr)
  | PtrMemberShift of (Sym.t * Id.t * 'TY pexpr)
  | Memcpy of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Memcmp of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Realloc of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Va_start of ('TY pexpr * 'TY pexpr)
  | Va_copy of 'TY pexpr
  | Va_arg of ('TY pexpr * act)
  | Va_end of 'TY pexpr
  | CopyAllocId of ('TY pexpr * 'TY pexpr)

type 'TY expr_ =
  | Epure of 'TY pexpr
  | Ememop of 'TY memop
  | Eaction of 'TY paction
  | Eskip
  | Eccall of act * 'TY pexpr * 'TY pexpr list
  | Elet of 'TY pattern * 'TY pexpr * 'TY expr
  | Eunseq of 'TY expr list
  | Ewseq of 'TY pattern * 'TY expr * 'TY expr
  | Esseq of 'TY pattern * 'TY expr * 'TY expr
  | Eif of 'TY pexpr * 'TY expr * 'TY expr
  | Ebound of 'TY expr
  | End of 'TY expr list
  | Erun of Sym.t * 'TY pexpr list
  | CN_progs of
      (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement list
      * Cnprog.t list

and 'TY expr = Expr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY expr_

val is_undef_or_error_expr : 'a expr -> bool

val bt_of_expr : 'TY expr -> 'TY

val loc_of_expr : 'a expr -> Locations.t

type 'TY globs =
  | GlobalDef of Sctypes.t * 'TY expr
  | GlobalDecl of Sctypes.t

type 'i arguments_l =
  | Define of (Sym.t * IndexTerms.t) * Locations.info * 'i arguments_l
  | Resource of
      (Sym.t * (ResourceTypes.t * BaseTypes.t)) * Locations.info * 'i arguments_l
  | Constraint of LogicalConstraints.t * Locations.info * 'i arguments_l
  | I of 'i

val mDefine : (Sym.t * IndexTerms.t) * Locations.info -> 'a arguments_l -> 'a arguments_l

val mConstraint
  :  LogicalConstraints.t * Locations.info ->
  'a arguments_l ->
  'a arguments_l

val mConstraints
  :  (LogicalConstraints.t * Locations.info) list ->
  'a arguments_l ->
  'a arguments_l

val mResource
  :  (Sym.t * (ResourceTypes.t * BaseTypes.t)) * Locations.info ->
  'a arguments_l ->
  'a arguments_l

val mResources
  :  ((Sym.t * (ResourceTypes.t * BaseTypes.t)) * Locations.info) list ->
  'a arguments_l ->
  'a arguments_l

type 'i arguments =
  | Computational of (Sym.t * BaseTypes.t) * Locations.info * 'i arguments
  | L of 'i arguments_l

val mComputational
  :  (Sym.t * BaseTypes.t) * Locations.info ->
  'a arguments ->
  'a arguments

val dtree_of_arguments
  :  ('a -> Cerb_frontend.Pp_ast.doc_tree) ->
  'a arguments ->
  Cerb_frontend.Pp_ast.doc_tree

type parse_ast_label_spec =
  { label_spec : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list }

type 'TY label_def =
  | Return of Locations.t
  | Label of
      Locations.t
      * 'TY expr arguments
      * Cerb_frontend.Annot.annot list
      * parse_ast_label_spec

type trusted =
  | Trusted of Locations.t
  | Checked

type desugared_spec =
  { accesses : (Sym.t * Cerb_frontend.Ctype.ctype) list;
    requires : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list;
    ensures : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list
  }

type 'TY args_and_body =
  ('TY expr * (Sym.t, 'TY label_def) Pmap.map * ReturnTypes.t) arguments

type 'TY fun_map_decl =
  | Proc of
      { loc : Locations.t;
        args_and_body : 'TY args_and_body;
        trusted : trusted;
        desugared_spec : desugared_spec
      }
  | ProcDecl of Locations.t * ArgumentTypes.ft option

type tag_definition =
  | StructDef of Memory.struct_layout
  | UnionDef

type function_to_convert =
  { loc : Locations.t;
    c_fun_sym : Sym.t;
    l_fun_sym : Sym.t
  }

type datatype =
  { loc : Locations.t;
    cases : (Sym.t * (Id.t * BaseTypes.t) list) list
  }

type 'TY file =
  { main : Sym.t option;
    tagDefs : (Sym.t, tag_definition) Pmap.map;
    globs : (Sym.t * 'TY globs) list;
    funs : (Sym.t, 'TY fun_map_decl) Pmap.map;
    extern : Cerb_frontend.Core.extern_map;
    stdlib_syms : Set.Make(Sym).t;
    mk_functions : function_to_convert list;
    resource_predicates : (Sym.t * ResourcePredicates.definition) list;
    logical_predicates : (Sym.t * LogicalFunctions.definition) list;
    datatypes : (Sym.t * datatype) list;
    lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
    call_funinfo : (Sym.t, Sctypes.c_concrete_sig) Pmap.map
  }
