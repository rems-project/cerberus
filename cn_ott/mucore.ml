(* generated by Ott 0.31 from: mucore.ott *)


type 
base_type =  (* base types *)
   Unit (* unit *)
 | Bool (* boolean *)
 | Integer (* integer *)
 | Read (* rational numbers? *)
 | Loc (* location *)
 | Array of base_type (* array *)
 | ListTy of base_type (* list *)
 | TupleTy of (base_type) list (* tuple *)
 | Struct of tag (* struct *)
 | Set of base_type (* set *)
 | Option of base_type (* option *)
 | ParamTy of base_type * base_type (* parameter types *)


(** subrules *)
let is_bool_binop_of_binop (binop5:Core.binop) : bool =
  match binop5 with
  | OpAdd -> false
  | OpSub -> false
  | OpMul -> false
  | OpDiv -> false
  | OpRem_t -> false
  | OpRem_f -> false
  | OpExp -> false
  | OpEq -> false
  | OpGt -> false
  | OpLt -> false
  | OpGe -> false
  | OpLe -> false
  | OpAnd -> (true)
  | OpOr -> (true)


let is_arith_binop_of_binop (binop5:Core.binop) : bool =
  match binop5 with
  | OpAdd -> (true)
  | OpSub -> (true)
  | OpMul -> (true)
  | OpDiv -> (true)
  | OpRem_t -> (true)
  | OpRem_f -> (true)
  | OpExp -> (true)
  | OpEq -> false
  | OpGt -> false
  | OpLt -> false
  | OpGe -> false
  | OpLe -> false
  | OpAnd -> false
  | OpOr -> false


let is_rel_binop_of_binop (binop5:Core.binop) : bool =
  match binop5 with
  | OpAdd -> false
  | OpSub -> false
  | OpMul -> false
  | OpDiv -> false
  | OpRem_t -> false
  | OpRem_f -> false
  | OpExp -> false
  | OpEq -> (true)
  | OpGt -> (true)
  | OpLt -> (true)
  | OpGe -> (true)
  | OpLe -> (true)
  | OpAnd -> false
  | OpOr -> false



type 
'TY mu_object_value =  (* C object values (inhabitants of object types), which can be read/stored *)
   M_OVinteger of Impl_mem.integer_value (* integer value *)
 | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
 | M_OVarray of ('TY mu_loaded_value) list (* C array value *)
 | M_OVstruct of Symbol.sym * ((Symbol.identifier * T.ct * Impl_mem.mem_value)) list (* C struct value *)
 | M_OVunion of Symbol.sym * Symbol.identifier * Impl_mem.mem_value (* C union value *)

and 'TY mu_loaded_value =  (* potentially unspecified C object values *)
   M_LVspecified of 'TY mu_object_value (* specified loaded value *)


type 
mu_ctor_val =  (* data constructors *)
   M_Cnil of T.bt (* empty list *)
 | M_Ccons (* list cons *)
 | M_Ctuple (* tuple *)
 | M_Carray (* C array *)
 | M_Cspecified (* non-unspecified loaded value *)


type 
'TY mu_value =  (* Core values *)
   M_Vobject of 'TY mu_object_value (* C object value *)
 | M_Vloaded of 'TY mu_loaded_value (* loaded C object value *)
 | M_Vunit (* unit *)
 | M_Vtrue (* boolean true *)
 | M_Vfalse (* boolean false *)
 | M_Vlist of T.bt * ('TY mu_value) list (* list *)
 | M_Vtuple of ('TY mu_value) list (* tuple *)


type 
mu_ctor_expr =  (* data constructors *)
   M_Civmax (* max integer value *)
 | M_Civmin (* min integer value *)
 | M_Civsizeof (* sizeof value *)
 | M_Civalignof (* alignof value *)
 | M_CivCOMPL (* bitwise complement *)
 | M_CivAND (* bitwise AND *)
 | M_CivOR (* bitwise OR *)
 | M_CivXOR (* bitwise XOR *)
 | M_Cfvfromint (* cast integer to floating value *)
 | M_Civfromfloat (* cast floating to integer value *)


type 
'TY mu_pval =  (* pure values *)
   M_PVsym of Symbol.sym (* Core identifier *)
 | M_PVimpl of Implementation.implementation_constant (* implementation-defined constant *)
 | M_PVmu_val of 'TY mu_value (* Core values *)
 | M_PVconstrained of ((Mem.mem_iv_constraint * 'TY mu_pval_aux)) list (* constrained value *)
 | M_PVerror of string * 'TY mu_pval_aux (* impl-defined static error *)
 | M_PVctor of mu_ctor_val * ('TY mu_pval_aux) list (* data constructor application *)
 | M_PVstruct of Symbol.sym * ((Symbol.identifier * 'TY mu_pval_aux)) list (* C struct expression *)
 | M_PVunion of Symbol.sym * Symbol.identifier * 'TY mu_pval_aux (* C union expression *)

and 'TY mu_pval_aux =  (* pure values with auxiliary info *)
   M_Pval of Location_ocaml.t * annot list * 'TY * 'TY mu_pval
 | M_Pval_no_aux of 'TY mu_pval (* Ott-hack for simpler typing rules *)


(** subrules *)
let is_mu_name_of_mu_pval (mu_pval5:'TY mu_pval) : bool =
  match mu_pval5 with
  | (M_PVsym symbol_sym) -> (true)
  | (M_PVimpl impl_const) -> (true)
  | (M_PVmu_val mu_value) -> false
  | (M_PVconstrained (mem_mem_iv_constraint_mu_pval_aux_list)) -> false
  | (M_PVerror (ty_string,mu_pval_aux)) -> false
  | (M_PVctor (mu_ctor_val,(mu_pval_aux_list))) -> false
  | (M_PVstruct (symbol_sym,(symbol_identifier_mu_pval_aux_list))) -> false
  | (M_PVunion (symbol_sym,symbol_identifier,mu_pval_aux)) -> false


let is_mu_pexpr_of_mu_pexpr (mu_pexpr5:'TY mu_pexpr) : bool =
  match mu_pexpr5 with
  | (M_PEpval mu_pval_aux) -> (true)
  | (M_PEctor (mu_ctor_expr,(mu_pval_aux_list))) -> ((List.for_all (fun mu_pval_aux_ -> true) mu_pval_aux_list))
  | (M_PEarray_shift (mu_pval_aux1,t_ct,mu_pval_aux2)) -> (true)
  | (M_PEmember_shift (mu_pval_aux,symbol_sym,symbol_identifier)) -> (true)
  | (M_PEnot mu_pval_aux) -> (true)
  |  (M_PEop ( binop , mu_pval_aux1 , mu_pval_aux2 ) )  -> (true)
  | (M_PEmemberof (symbol_sym,symbol_identifier,mu_pval_aux)) -> (true)
  | (M_PEcall (mu_name,(mu_pval_aux_list))) -> ((is_mu_name_of_mu_pval mu_name) && (List.for_all (fun mu_pval_aux_ -> true) mu_pval_aux_list))
  | (M_PEassert_undef (mu_pval_aux,ty_loc,uB_name)) -> (true)
  | (M_PEbool_to_integer mu_pval_aux) -> (true)
  | (M_PEconv_int (ty_act,mu_pval_aux)) -> (true)
  | (M_PEwrapI (ty_act,mu_pval_aux)) -> (true)


let is_mu_pexpr_aux_of_mu_pexpr_aux (mu_pexpr_aux5:'TY mu_pexpr_aux) : bool =
  match mu_pexpr_aux5 with
  | (M_Pexpr (ty_loc,annots,tyvar_TY,mu_pexpr)) -> ((is_mu_pexpr_of_mu_pexpr mu_pexpr))
  | (M_Pexpr_no_aux mu_pexpr) -> ((is_mu_pexpr_of_mu_pexpr mu_pexpr))


let is_mu_seq_expr_of_mu_seq_expr (mu_seq_expr5:'TY mu_seq_expr) : bool =
  match mu_seq_expr5 with
  | (M_Seq_Epexpr mu_pexpr_aux) -> ((is_mu_pexpr_aux_of_mu_pexpr_aux mu_pexpr_aux))
  | (M_Seq_Eccall (ty_act,mu_pval_aux,(spine_elem_list))) -> ((List.for_all (fun spine_elem_ -> true) spine_elem_list))
  | (M_Seq_Eproc (mu_name,(spine_elem_list))) -> ((is_mu_name_of_mu_pval mu_name) && (List.for_all (fun spine_elem_ -> true) spine_elem_list))


let is_mu_seq_expr_aux_of_mu_seq_expr_aux (mu_seq_expr_aux5:'TY mu_seq_expr_aux) : bool =
  match mu_seq_expr_aux5 with
  | (M_Seq_expr (ty_loc,annots,mu_seq_expr)) -> ((is_mu_seq_expr_of_mu_seq_expr mu_seq_expr))
  | (M_Seq_no_aux mu_seq_expr) -> ((is_mu_seq_expr_of_mu_seq_expr mu_seq_expr))



type 
'TY mu_pexpr =  (* pure expressions *)
   M_PEpval of 'TY mu_pval_aux (* pure values *)
 | M_PEctor of mu_ctor_expr * ('TY mu_pval_aux) list (* data constructor application *)
 | M_PEarray_shift of 'TY mu_pval_aux * T.ct * 'TY mu_pval_aux (* pointer array shift *)
 | M_PEmember_shift of 'TY mu_pval_aux * Symbol.sym * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'TY mu_pval_aux (* boolean not *)
 | M_PEop of Core.binop * 'TY mu_pval_aux * 'TY mu_pval_aux (* binary operations *)
 | M_PEmemberof of Symbol.sym * Symbol.identifier * 'TY mu_pval_aux (* C struct/union member access *)
 | M_PEcall of 'TY mu_pval * ('TY mu_pval_aux) list (* pure function call *)
 | M_PEassert_undef of 'TY mu_pval_aux * Location_ocaml.t * Undefined.undefined_behaviour
 | M_PEbool_to_integer of 'TY mu_pval_aux
 | M_PEconv_int of 'TY act * 'TY mu_pval_aux
 | M_PEwrapI of 'TY act * 'TY mu_pval_aux


type 
m_kill_kind = 
   M_Dynamic
 | M_Static of T.ct


type 
'TY mu_pexpr_aux =  (* pure expressions with location and annotations *)
   M_Pexpr of Location_ocaml.t * annot list * 'TY * 'TY mu_pexpr
 | M_Pexpr_no_aux of 'TY mu_pexpr (* Ott-hack for simpler typing rules *)


type 
mu_pattern = 
   M_CaseBase of ( Symbol.sym option * T.bt )
 | M_CaseCtor of mu_ctor_val * (mu_pattern_aux) list

and mu_pattern_aux = 
   M_Pattern of Location_ocaml.t * annot list * mu_pattern
 | M_Pat_no_aux of mu_pattern (* Ott-hack for simpler typing rules *)


type 
'TY mu_tpval =  (* top-level pure values *)
   M_TPVundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_TPVdone of 'TY mu_pval_aux (* pure done *)


type 
'TY mu_sym_or_pattern = 
   M_Symbol of Symbol.sym
 | M_Pat of mu_pattern_aux


type 
'TY mu_tpval_aux =  (* top-level pure values with location and annotations *)
   M_TPval of Location_ocaml.t * annot list * 'TY * 'TY mu_tpval
 | M_TPval_no_aux of 'TY mu_tpval (* Ott-hack for simpler typing rules *)


type 
'TY mu_tpexpr =  (* top-level pure expressions *)
   M_TPEtpval of 'TY mu_tpval_aux (* top-level pure values *)
 | M_TPEcase of 'TY mu_pval_aux * ((mu_pattern_aux * 'TY mu_tpexpr_aux)) list (* pattern matching *)
 | M_TPElet of 'TY mu_sym_or_pattern * 'TY mu_pexpr_aux * 'TY mu_tpexpr_aux (* pure let *)
 | M_TPEif of 'TY mu_pval_aux * 'TY mu_tpexpr_aux * 'TY mu_tpexpr_aux (* pure if *)

and 'TY mu_tpexpr_aux =  (* pure top-level pure expressions with auxiliary info *)
   M_TPexpr of Location_ocaml.t * annot list * 'TY * 'TY mu_tpexpr
 | M_TPexpr_no_aux of 'TY mu_tpexpr (* Ott-hack for simpler typing rules *)


type 
lit = 
   Lit_Sym of Symbol.sym
 | Lit_Unit
 | Lit_Bool of bool
 | Lit_Z of Z.t
 | Lit_Q of ( int * int )


type 
'bt bool_op = 
   Not of 'bt term_aux
 | Eq of 'bt term_aux * 'bt term_aux
 | And of ('bt term_aux) list
 | Or of ('bt term_aux) list
 | ITE of 'bt term_aux * 'bt term_aux * 'bt term_aux

and 'bt arith_op = 
   Add of 'bt term_aux * 'bt term_aux
 | Sub of 'bt term_aux * 'bt term_aux
 | Mul of 'bt term_aux * 'bt term_aux
 | Div of 'bt term_aux * 'bt term_aux
 | Rem_t of 'bt term_aux * 'bt term_aux
 | Rem_f of 'bt term_aux * 'bt term_aux
 | Exp of 'bt term_aux * 'bt term_aux

and 'bt cmp_op = 
   LT of 'bt term_aux * 'bt term_aux (* less than *)
 | LE of 'bt term_aux * 'bt term_aux (* less than or equal *)

and 'bt list_op = 
   Nil
 | Tail of 'bt term_aux
 | NthList of int * 'bt term_aux

and 'bt tuple_op = 
   Tuple of ('bt term_aux) list
 | NthTuple of int * 'bt term_aux

and 'bt pointer_op = 
   Null of Impl_mem.pointer_value
 | AddPointer of 'bt term_aux * 'bt term_aux
 | IntegerToPointerCast of 'bt term_aux
 | PointerToIntegerCast of 'bt term_aux

and 'bt option_op = 
   Nothing of BT.t
 | Something of 'bt term_aux

and 'bt array_op = 
   ArrayGet of 'bt term_aux * 'bt term_aux

and 'bt param_op = 
   Param of Symbol.sym * base_type * 'bt term_aux
 | App of 'bt term_aux * ('bt term_aux) list

and 'bt struct_op = 
   StructMember of tag * 'bt term_aux * Symbol.identifier

and 'bt ct_pred = 
   Representable of Sctypes.t * 'bt term_aux
 | Aligned of Sctypes.t * 'bt term_aux
 | AlignedI of 'bt term_aux * 'bt term_aux

and 'bt term = 
   Lit of lit
 | Arith_op of 'bt arith_op
 | Bool_op of 'bt bool_op
 | Cmp_op of 'bt cmp_op
 | Tuple_op of 'bt tuple_op
 | Struct_op of 'bt struct_op
 | Pointer_op of 'bt pointer_op
 | List_op of 'bt list_op
 | Array_op of 'bt array_op
 | CT_pred of 'bt ct_pred
 | Option_op of 'bt option_op
 | Param_op of 'bt param_op

and 'bt term_aux =  (* terms with auxiliary info *)
   IT of 'bt term * 'bt
 | IT_no_aux of 'bt term (* Ott-hack for simpler typing rules *)


type 
res_term =  (* resource terms *)
   ResT_Empty (* empty heap *)
 | ResT_PointsTo (* single-cell heap *)
 | ResT_Var of Symbol.sym (* variable *)
 | ResT_SepPair of res_term * res_term (* seperating-conjunction pair *)
 | ResT_Pack of 'TY mu_pval_aux * res_term (* packing for existentials *)


type 
spine_elem =  (* spine element *)
   Spine_Elem_pure_val of 'TY mu_pval_aux (* pure value *)
 | Spine_Elem_logical_val of 'bt term_aux (* logical value *)
 | Spine_Elem_res_val of res_term (* resource value *)


type 
'TY mu_action =  (* memory actions *)
   M_Create of 'TY mu_pval_aux * 'TY act * Symbol.prefix
 | M_CreateReadOnly of 'TY mu_pval_aux * 'TY act * 'TY mu_pval_aux * Symbol.prefix
 | M_Alloc of 'TY mu_pval_aux * 'TY mu_pval_aux * Symbol.prefix
 | M_Kill of m_kill_kind * 'TY mu_pval_aux
 | M_Store of bool * 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * Cmm_csem.memory_order (* true means store is locking *)
 | M_Load of 'TY act * 'TY mu_pval_aux * Cmm_csem.memory_order
 | M_RMW of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of 'TY act * 'TY mu_pval_aux * Linux.linux_memory_order
 | M_LinuxStore of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * Linux.linux_memory_order
 | M_LinuxRMW of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux * Linux.linux_memory_order


type 
resource =  (* resources *)
   Res_Empty (* empty heap *)
 | Res_Points_to of type points_to = { pointer: 'bt term; perm : int * int; init: bool; ct = Sctypes.t; pointee : 'bt term; } (* points-top heap pred. *)
 | Res_SepConj of resource * resource (* seperating conjunction *)
 | Res_Exists of Symbol.sym * base_type * resource (* existential *)
 | Res_Term of 'bt term_aux * resource (* logical conjuction *)


type 
'TY mu_seq_expr =  (* sequential (effectful) expressions *)
   M_Seq_Epexpr of 'TY mu_pexpr_aux (* pure expressions *)
 | M_Seq_Eccall of 'TY act * 'TY mu_pval_aux * (spine_elem) list (* C function call *)
 | M_Seq_Eproc of 'TY mu_pval * (spine_elem) list (* procedure call *)


type 
'TY mu_action_aux =  (* memory actions with auxiliary info *)
   M_Action of Location_ocaml.t * 'TY mu_action
 | M_no_aux of 'TY mu_action (* Ott-hack for simpler typing rules *)


type 
res_pattern =  (* resource terms *)
   ResP_Empty (* empty heap *)
 | ResP_PointsTo (* single-cell heap *)
 | ResP_Var of Symbol.sym (* variable *)
 | ResP_SepPair of res_pattern * res_pattern (* seperating-conjunction pair *)
 | ResP_Pack of Symbol.sym * res_pattern (* packing for existentials *)


type 
ret =  (* return types *)
   RetTy_Computational of 'sym * base_type * ret
 | RetTy_Logical of 'sym * base_type * ret
 | RetTy_Resource of resource * ret
 | RetTy_Constraint of 'bt term_aux * ret
 | RetTy_I


type 
'TY mu_tval =  (* (effectful) top-level values *)
   M_TVdone of (spine_elem) list (* end of top-level expression *)
 | M_TVundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)


type 
'TY mu_memop =  (* operations involving the memory state *)
   M_PtrEq of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer equality comparison *)
 | M_PtrNe of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer inequality comparison *)
 | M_PtrLt of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer less-than comparison *)
 | M_PtrGt of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer greater-than comparison *)
 | M_PtrLe of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer less-than comparison *)
 | M_PtrGe of 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer greater-than comparison *)
 | M_Ptrdiff of 'TY act * 'TY mu_pval_aux * 'TY mu_pval_aux (* pointer subtraction *)
 | M_IntFromPtr of 'TY act * 'TY act * 'TY mu_pval_aux (* cast of pointer value to integer value *)
 | M_PtrFromInt of 'TY act * 'TY act * 'TY mu_pval_aux (* cast of integer value to pointer value *)
 | M_PtrValidForDeref of 'TY act * 'TY mu_pval_aux (* dereferencing validity predicate *)
 | M_PtrWellAligned of 'TY act * 'TY mu_pval_aux
 | M_PtrArrayShift of 'TY mu_pval_aux * 'TY act * 'TY mu_pval_aux
 | M_Memcpy of 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux
 | M_Memcmp of 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux
 | M_Realloc of 'TY mu_pval_aux * 'TY mu_pval_aux * 'TY mu_pval_aux
 | M_Va_start of 'TY mu_pval_aux * 'TY mu_pval_aux
 | M_Va_copy of 'TY mu_pval_aux
 | M_Va_arg of 'TY mu_pval_aux * 'TY act
 | M_Va_end of 'TY mu_pval_aux


type 
'TY mu_seq_expr_aux =  (* sequential (effectful) expressions with auxiliary info *)
   M_Seq_expr of Location_ocaml.t * annot list * 'TY mu_seq_expr
 | M_Seq_no_aux of 'TY mu_seq_expr (* Ott-hack for simpler typing rules *)


type 
'TY mu_paction =  (* memory actions with polarity *)
   M_Paction of Core.polarity * 'TY mu_action_aux


type 
ret_pattern =  (* return pattern *)
   RetP_computational of 'TY mu_sym_or_pattern (* computational variable *)
 | RetP_logical of Symbol.sym (* logical variable *)
 | RetP_resource of res_pattern (* resource variable *)


type 
'TY mu_tval_aux =  (* (effectful) top-level values with auxiliary info *)
   M_Tval of Location_ocaml.t * annot list * 'TY mu_tval
 | M_Tno_aux of 'TY mu_tval (* Ott-hack for simpler typing rules *)


type 
'TY mu_seq_texpr =  (* sequential top-level (effectful) expressions *)
   M_Seq_TEtval of 'TY mu_tval (* (effectful) top-level values *)
 | M_Seq_TErun of Symbol.sym * ('TY mu_pval_aux) list (* run from label *)
 | M_Seq_TElet of (ret_pattern) list * 'TY mu_seq_expr_aux * 'TY mu_texpr (* bind return patterns *)
 | M_Seq_TEletT of (ret_pattern) list * ret * 'TY mu_texpr * 'TY mu_texpr (* annotated bind return patterns *)
 | M_Seq_TEcase of 'TY mu_pval_aux * ((mu_pattern_aux * 'TY mu_texpr)) list (* pattern matching *)
 | M_Seq_TEif of 'TY mu_pval_aux * 'TY mu_texpr * 'TY mu_texpr (* conditional *)
 | M_Seq_TEbound of int * 'TY mu_is_texpr_aux (* limit scope of indet seq behaviour, absent at runtime *)

and 'TY mu_seq_texpr_aux =  (* sequential top-level (effectful) expressions with auxiliary info *)
   M_Seq_Texpr of Location_ocaml.t * annot list * 'TY mu_seq_texpr
 | M_Seq_Tseq_no_aux of 'TY mu_seq_texpr (* Ott-hack for simpler typing rules *)

and 'TY mu_is_expr =  (* indet seq (effectful) expressions *)
   M_Is_Ememop of 'TY mu_memop (* pointer op involving memory *)
 | M_Is_Eaction of 'TY mu_paction (* memory action *)
 | M_Is_Eunseq of (('TY mu_texpr * ret)) list (* unsequenced expressions *)

and 'TY mu_is_expr_aux =  (* indet seq (effectful) expressions with auxiliary info *)
   M_Is_expr of Location_ocaml.t * annot list * 'TY mu_is_expr
 | M_Is_no_aux of 'TY mu_is_expr (* Ott-hack for simpler typing rules *)

and 'TY mu_is_texpr =  (* indet seq top-level (effectful) expressions *)
   M_is_TEwseq of mu_pattern_aux * 'TY mu_is_expr_aux * 'TY mu_texpr (* weak sequencing *)
 | M_is_TEsseq of 'TY mu_sym_or_pattern * 'TY mu_is_expr_aux * 'TY mu_texpr (* strong sequencing *)

and 'TY mu_is_texpr_aux =  (* indet seq top-level (effectful) expressions with auxiliary info *)
   M_Is_Texpr of Location_ocaml.t * annot list * 'TY mu_is_texpr
 | M_Is_Tno_aux of 'TY mu_is_texpr (* Ott-hack for simpler typing rules *)

and 'TY mu_texpr =  (* top-level (effectful) expressions *)
   M_TESeq of 'TY mu_seq_texpr_aux (* sequential (effectful) expressions *)
 | M_TEIS of 'TY mu_is_texpr_aux (* indet seq (effectful) expressions *)


type 
rets =  (* concatenation of return types *)
   RetTys_Concat of (ret) list


type 
arg =  (* argument/function types *)
   ArgTy_Computational of 'sym * base_type * arg
 | ArgTy_Logical of 'sym * base_type * arg
 | ArgTy_Resource of resource * arg
 | ArgTy_Constraint of 'bt term_aux * arg
 | ArgTy_Ret of ret


(** subrules *)
let rec is_pure_ret_of_ret (_r5:ret) : bool =
  match _r5 with
  | (RetTy_Computational (tyvar_sym,base_type,ret)) -> ((is_pure_ret_of_ret ret))
  | (RetTy_Logical (tyvar_sym,base_type,ret)) -> false
  | (RetTy_Resource (resource,ret)) -> false
  | (RetTy_Constraint (term_aux,ret)) -> ((is_pure_ret_of_ret ret))
  | RetTy_I -> (true)


let rec is_pure_arg_of_arg (arg5:arg) : bool =
  match arg5 with
  | (ArgTy_Computational (tyvar_sym,base_type,arg)) -> ((is_pure_arg_of_arg arg))
  | (ArgTy_Logical (tyvar_sym,base_type,arg)) -> false
  | (ArgTy_Resource (resource,arg)) -> false
  | (ArgTy_Constraint (term_aux,arg)) -> ((is_pure_arg_of_arg arg))
  | (ArgTy_Ret ret) -> ((is_pure_ret_of_ret ret))


(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)
(** definitions *)


