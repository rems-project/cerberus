(* generated by Ott 0.31 from: mucore.ott *)


type 
base_type =  (* Core base types *)
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
 | Param of (base_type) list * base_type (* parameter types *)


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
mu_ctor =  (* data constructors *)
   M_Cnil of T.bt (* empty list *)
 | M_Ccons (* list cons *)
 | M_Ctuple (* tuple *)
 | M_Carray (* C array *)
 | M_Civmax (* max integer value *)
 | M_Civmin (* min integer value *)
 | M_Civsizeof (* sizeof value *)
 | M_Civalignof (* alignof value *)
 | M_CivCOMPL (* bitwise complement *)
 | M_CivAND (* bitwise AND *)
 | M_CivOR (* bitwise OR *)
 | M_CivXOR (* bitwise XOR *)
 | M_Cspecified (* non-unspecified loaded value *)
 | M_Cunspecified (* unspecified loaded value *)
 | M_Cfvfromint (* cast integer to floating value *)
 | M_Civfromfloat (* cast floating to integer value *)


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
mu_pattern_aux = 
   M_CaseBase of ( Symbol.sym option * T.bt )
 | M_CaseCtor of mu_ctor * (mu_pattern) list

and mu_pattern = 
   M_Pattern of Location_ocaml.t * annot list * mu_pattern_aux


type 
'TY mu_sym_or_pattern = 
   M_Symbol of Symbol.sym
 | M_Pat of mu_pattern


type 
'TY mu_pexpr_aux =  (* pure expressions *)
   M_PEsym of Symbol.sym
 | M_PEimpl of Implementation.implementation_constant (* implementation-defined constant *)
 | M_PEval of 'TY mu_value
 | M_PEconstrained of ((Mem.mem_iv_constraint * 'TY asym)) list (* constrained value *)
 | M_PEerror of string * 'TY asym (* impl-defined static error *)
 | M_PEctor of mu_ctor * ('TY asym) list (* data constructor application *)
 | M_PEarray_shift of 'TY asym * T.ct * 'TY asym (* pointer array shift *)
 | M_PEmember_shift of 'TY asym * Symbol.sym * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'TY asym (* boolean not *)
 | M_PEop of Core.binop * 'TY asym * 'TY asym (* binary operations *)
 | M_PEstruct of Symbol.sym * ((Symbol.identifier * 'TY asym)) list (* C struct expression *)
 | M_PEunion of Symbol.sym * Symbol.identifier * 'TY asym (* C union expression *)
 | M_PEmemberof of Symbol.sym * Symbol.identifier * 'TY asym (* C struct/union member access *)
 | M_PEcall of Symbol.sym Core.generic_name * ('TY asym) list (* pure function call *)
 | M_PEassert_undef of 'TY asym * Location_ocaml.t * Undefined.undefined_behaviour
 | M_PEbool_to_integer of 'TY asym
 | M_PEconv_int of 'TY act * 'TY asym
 | M_PEwrapI of 'TY act * 'TY asym


type 
'TY mu_pexpr =  (* pure expressions with location and annotations *)
   M_Pexpr of Location_ocaml.t * annot list * 'TY * 'TY mu_pexpr_aux


type 
m_kill_kind = 
   M_Dynamic
 | M_Static of T.ct


type 
'TY mu_tpexpr_aux =  (* top-level pure expressions *)
   M_TPundef of Location_ocaml.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_TPcase of 'TY asym * ((mu_pattern * 'TY mu_tpexpr)) list (* pattern matching *)
 | M_TPlet of 'TY mu_sym_or_pattern * 'TY mu_tpexpr * 'TY mu_tpexpr (* pure let *)
 | M_TPif of 'TY asym * 'TY mu_tpexpr * 'TY mu_tpexpr (* pure if *)
 | M_TPdone of 'TY asym (* pure done *)

and 'TY mu_tpexpr =  (* pure top-level pure expressions with location and annotations *)
   M_TPexpr of Location_ocaml.t * annot list * 'TY * 'TY mu_tpexpr_aux


type 
lit = 
   Lit_Sym of x
 | Lit_Unit
 | Lit_Bool of bool
 | Lit_Z of Z.t
 | Lit_Pointer of Z.t


type 
'bt pointer_op = 
   Null


type 
'bt bool_op = 
   Not of 'bt index_term
 | Eq of 'bt index_term * 'bt index_term
 | And of ('bt index_term) list

and 'bt list_op = 
   List of ('bt index_term) list
 | NthList of int * 'bt index_term

and 'bt array_op = 
   ArrayGet of 'bt index_term * Z.t

and 'bt param_op = 
   App of 'bt index_term * ('bt index_term) list

and 'bt index_term_aux = 
   Bool_op of 'bt bool_op
 | List_op of 'bt list_op
 | Pointer_op of 'bt pointer_op
 | Array_op of 'bt array_op
 | Param_op of 'bt param_op

and 'bt index_term = 
   Lit of lit
 | IT of 'bt index_term_aux * 'bt


type 
'TY mu_memop =  (* operations involving the memory state *)
   M_PtrEq of 'TY asym * 'TY asym (* pointer equality comparison *)
 | M_PtrNe of 'TY asym * 'TY asym (* pointer inequality comparison *)
 | M_PtrLt of 'TY asym * 'TY asym (* pointer less-than comparison *)
 | M_PtrGt of 'TY asym * 'TY asym (* pointer greater-than comparison *)
 | M_PtrLe of 'TY asym * 'TY asym (* pointer less-than comparison *)
 | M_PtrGe of 'TY asym * 'TY asym (* pointer greater-than comparison *)
 | M_Ptrdiff of 'TY act * 'TY asym * 'TY asym (* pointer subtraction *)
 | M_IntFromPtr of 'TY act * 'TY act * 'TY asym (* cast of pointer value to integer value *)
 | M_PtrFromInt of 'TY act * 'TY act * 'TY asym (* cast of integer value to pointer value *)
 | M_PtrValidForDeref of 'TY act * 'TY asym (* dereferencing validity predicate *)
 | M_PtrWellAligned of 'TY act * 'TY asym
 | M_PtrArrayShift of 'TY asym * 'TY act * 'TY asym
 | M_Memcpy of 'TY asym * 'TY asym * 'TY asym
 | M_Memcmp of 'TY asym * 'TY asym * 'TY asym
 | M_Realloc of 'TY asym * 'TY asym * 'TY asym
 | M_Va_start of 'TY asym * 'TY asym
 | M_Va_copy of 'TY asym
 | M_Va_arg of 'TY asym * 'TY act
 | M_Va_end of 'TY asym


type 
'TY mu_paction =  (* memory actions with polarity *)
   

type 
c =  (* computational var env *)
   Comp_empty
 | Comp_cons of c * x * base_type


type 
n =  (* constraints env *)
   Con_empty
 | Con_cons of n


type 
l =  (* logical var env *)
   Log_empty
 | Log_cons of l * x


type 
ret =  (* return types *)
   RetTy_Computational of x * base_type * ret
 | RetTy_Logical of x * ret
 | RetTy_Resource of ret
 | RetTy_Constraint of 'bt index_term * ret
 | RetTy_I


type 
'TY mu_expr_aux =  (* (effectful) expressions *)
   M_Epure of 'TY mu_pexpr
 | M_Ememop of 'TY mu_memop (* pointer op involving memory *)
 | M_Eaction of 'TY mu_paction (* memory action *)
 | M_Eskip
 | M_Eccall of 'TY act * 'TY asym * ('TY asym) list (* C function call *)
 | M_Eproc of Symbol.sym Core.generic_name * ('TY asym) list (* Core procedure call *)


type 
'TY mu_expr =  (* (effectful) expressions with location and annotations *)
   M_EExpr of Location_ocaml.t * annot list * 'TY mu_expr_aux


type 
'TY mu_action_aux =  (* memory actions *)
   M_Create of 'TY asym * 'TY act * Symbol.prefix
 | M_CreateReadOnly of 'TY asym * 'TY act * 'TY asym * Symbol.prefix
 | M_Alloc of 'TY asym * 'TY asym * Symbol.prefix
 | M_Kill of m_kill_kind * 'TY asym (* the boolean indicates whether the action is dynamic (i.e. free()) *)
 | M_Store of bool * 'TY act * 'TY asym * 'TY asym * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
 | M_Load of 'TY act * 'TY asym * Cmm_csem.memory_order
 | M_RMW of 'TY act * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of 'TY act * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of 'TY act * 'TY asym * 'TY asym * 'TY asym * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of 'TY act * 'TY asym * Linux.linux_memory_order
 | M_LinuxStore of 'TY act * 'TY asym * 'TY asym * Linux.linux_memory_order
 | M_LinuxRMW of 'TY act * 'TY asym * 'TY asym * Linux.linux_memory_order


type 
'TY mu_texpr_aux =  (* top-level expressions *)
   M_Elet of 'TY mu_sym_or_pattern * 'TY mu_pexpr * 'TY mu_texpr
 | M_Ewseq of mu_pattern * 'TY mu_expr * 'TY mu_texpr (* weak sequencing *)
 | M_Esseq of 'TY mu_sym_or_pattern * 'TY mu_expr * 'TY mu_texpr (* strong sequencing *)
 | M_Ecase of 'TY asym * ((mu_pattern * 'TY mu_texpr)) list (* pattern matching *)
 | M_Eif of 'TY asym * 'TY mu_texpr * 'TY mu_texpr
 | M_Ebound of int * 'TY mu_texpr (* $\ldots$and boundary *)
 | M_Eunseq of ('TY mu_expr) list (* unsequenced expressions *)
 | M_End of ('TY mu_texpr) list (* nondeterministic sequencing *)
 | M_Edone of 'TY asym
 | M_Eundef of Location_ocaml.t * Undefined.undefined_behaviour
 | M_Erun of Symbol.sym * ('TY asym) list (* run from label *)

and 'TY mu_texpr =  (* top-level expressions with location and annotations *)
   M_TExpr of Location_ocaml.t * annot list * 'TY mu_texpr_aux


type 
arg =  (* argument types *)
   ArgTy_Computational of x * base_type * arg
 | ArgTy_Logical of x * arg
 | ArgTy_Resource of arg
 | ArgTy_Constraint of 'bt index_term * arg
 | ArgTy_I


type 
'TY mu_action = 
   M_Action of Location_ocaml.t * 'TY mu_action_aux


type 
'bt tuple_op = 
   Tuple of ('bt index_term) list
 | NthTuple of 'bt index_term * int


type 
'bt struct_op = 
   StructMember of tag * 'bt index_term * Symbol.identifier

(** definitions *)
(** definitions *)
(** definitions *)


