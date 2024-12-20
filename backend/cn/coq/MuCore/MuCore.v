(* Module Mucore - CN-specific variant of Cerberus Core 
   A more specialized version of Core – this is what CN actually uses. *)

Require Import String.
Require Import List.
Require Import ZArith.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Symbol.
Require Import Location.

(* We'll need to declare some types that are imported from other modules *)
Parameter Annot_t : Type.
Parameter Sctypes_t : Type.
Parameter Sym_t : Type.
Parameter Id_t : Type.
Parameter BaseTypes_t : Type.
Parameter IndexTerms_t : Type.
Parameter Request_t : Type.
Parameter mem_iv_constraint : Type.
Parameter binop : Type.
Parameter iop : Type.
Parameter undefined_behaviour : Type.
Parameter LogicalConstraints_t : Type.
Parameter cn_condition : Type.
Parameter ReturnTypes_t : Type.
Parameter ArgumentTypes_ft : Type.
Parameter Memory_struct_layout : Type.

(* Memory orders - we'll need to declare these as parameters since they come from other modules *)
Parameter memory_order : Type.
Parameter linux_memory_order : Type.
Parameter polarity : Type.

(* Annotated C type *)
Record act := {
  loc : Location_t;
  annot : list Annot_t;
  ct : Sctypes_t
}.

(* Object and value types - using mutual inductive definitions *)
Inductive integer_value : Type. (* placeholder *)
Inductive floating_value : Type. (* placeholder *)
Inductive pointer_value : Type. (* placeholder *)
Inductive mem_value : Type. (* placeholder *)

Inductive object_value_ (TY : Type) : Type :=
  | OVinteger : integer_value -> object_value_ TY
  | OVfloating : floating_value -> object_value_ TY
  | OVpointer : pointer_value -> object_value_ TY
  | OVarray : list (object_value TY) -> object_value_ TY
  | OVstruct : Sym_t -> list (Id_t * Sctypes_t * mem_value) -> object_value_ TY
  | OVunion : Sym_t -> Id_t -> mem_value -> object_value_ TY

with object_value (TY : Type) : Type :=
  | OV : TY -> object_value_ TY -> object_value TY.

Inductive value_ (TY : Type) : Type :=
  | Vobject : object_value TY -> value_ TY
  | Vctype : Type -> value_ TY  (* simplified from ctype *)
  | Vfunction_addr : Sym_t -> value_ TY
  | Vunit : value_ TY
  | Vtrue : value_ TY
  | Vfalse : value_ TY
  | Vlist : BaseTypes_t -> list (value TY) -> value_ TY
  | Vtuple : list (value TY) -> value_ TY

with value (TY : Type) : Type :=
  | V : TY -> value_ TY -> value TY.

(* Constructor types *)
Inductive ctor : Type :=
  | Cnil : BaseTypes_t -> ctor
  | Ccons : ctor
  | Ctuple : ctor
  | Carray : ctor.

(* Pattern types *)
Inductive pattern_ (TY : Type) : Type :=
  | CaseBase : option Sym_t * BaseTypes_t -> pattern_ TY
  | CaseCtor : ctor -> list (pattern TY) -> pattern_ TY

with pattern (TY : Type) : Type :=
  | Pattern : Location_t -> list Annot_t -> TY -> pattern_ TY -> pattern TY.

(* Function types *)
Inductive mu_function : Type :=
  | F_params_length : mu_function
  | F_params_nth : mu_function
  | F_are_compatible : mu_function
  | F_size_of : mu_function
  | F_align_of : mu_function
  | F_max_int : mu_function
  | F_min_int : mu_function
  | F_ctype_width : mu_function.

(* Bitwise operations *)
Inductive bw_binop : Type :=
  | BW_OR : bw_binop
  | BW_AND : bw_binop
  | BW_XOR : bw_binop.

Inductive bw_unop : Type :=
  | BW_COMPL : bw_unop
  | BW_CTZ : bw_unop
  | BW_FFS : bw_unop.

(* Bound kinds *)
Inductive bound_kind : Type :=
  | Bound_Wrap : act -> bound_kind
  | Bound_Except : act -> bound_kind.

(* Memory operations *)
Inductive m_kill_kind : Type :=
  | Dynamic : m_kill_kind
  | Static : Sctypes_t -> m_kill_kind.

(* Pure expressions *)
Inductive pexpr_ (TY: Type) : Type :=
  | PEsym : Sym_t -> pexpr_ TY
  | PEval : value TY -> pexpr_ TY 
  | PEconstrained : list (mem_iv_constraint * pexpr TY) -> pexpr_ TY
  | PEctor : ctor -> list (pexpr TY) -> pexpr_ TY
  | PEbitwise_unop : bw_unop -> pexpr TY -> pexpr_ TY
  | PEbitwise_binop : bw_binop -> pexpr TY -> pexpr TY -> pexpr_ TY
  | Cfvfromint : pexpr TY -> pexpr_ TY
  | Civfromfloat : act -> pexpr TY -> pexpr_ TY
  | PEarray_shift : pexpr TY -> Sctypes_t -> pexpr TY -> pexpr_ TY
  | PEmember_shift : pexpr TY -> Sym_t -> Id_t -> pexpr_ TY
  | PEnot : pexpr TY -> pexpr_ TY
  | PEop : binop -> pexpr TY -> pexpr TY -> pexpr_ TY
  | PEapply_fun : mu_function -> list (pexpr TY) -> pexpr_ TY
  | PEstruct : Sym_t -> list (Id_t * pexpr TY) -> pexpr_ TY
  | PEunion : Sym_t -> Id_t -> pexpr TY -> pexpr_ TY
  | PEcfunction : pexpr TY -> pexpr_ TY
  | PEmemberof : Sym_t -> Id_t -> pexpr TY -> pexpr_ TY
  | PEbool_to_integer : pexpr TY -> pexpr_ TY
  | PEconv_int : pexpr TY -> pexpr TY -> pexpr_ TY
  | PEconv_loaded_int : pexpr TY -> pexpr TY -> pexpr_ TY
  | PEwrapI : act -> pexpr TY -> pexpr_ TY
  | PEcatch_exceptional_condition : act -> pexpr TY -> pexpr_ TY
  | PEbounded_binop : bound_kind -> iop -> pexpr TY -> pexpr TY -> pexpr_ TY
  | PEis_representable_integer : pexpr TY -> act -> pexpr_ TY
  | PEundef : Location_t -> undefined_behaviour -> pexpr_ TY
  | PEerror : string -> pexpr TY -> pexpr_ TY
  | PElet : pattern TY -> pexpr TY -> pexpr TY -> pexpr_ TY
  | PEif : pexpr TY -> pexpr TY -> pexpr TY -> pexpr_ TY

with pexpr (TY: Type) : Type :=
  | Pexpr : Location_t -> list Annot_t -> TY -> pexpr_ TY -> pexpr TY.

(* Action types *)
Inductive action_ (TY : Type) : Type :=
  | Create : pexpr TY -> act -> Sym_t -> action_ TY
  | CreateReadOnly : pexpr TY -> act -> pexpr TY -> Sym_t -> action_ TY
  | Alloc : pexpr TY -> pexpr TY -> Sym_t -> action_ TY
  | Kill : m_kill_kind -> pexpr TY -> action_ TY
  | Store : bool -> act -> pexpr TY -> pexpr TY -> memory_order -> action_ TY
  | Load : act -> pexpr TY -> memory_order -> action_ TY
  | RMW : act -> pexpr TY -> pexpr TY -> pexpr TY -> memory_order -> memory_order -> action_ TY
  | Fence : memory_order -> action_ TY
  | CompareExchangeStrong : 
      act -> pexpr TY -> pexpr TY -> pexpr TY -> 
      memory_order -> memory_order -> action_ TY
  | CompareExchangeWeak :
      act -> pexpr TY -> pexpr TY -> pexpr TY ->
      memory_order -> memory_order -> action_ TY
  | LinuxFence : linux_memory_order -> action_ TY
  | LinuxLoad : act -> pexpr TY -> linux_memory_order -> action_ TY
  | LinuxStore : act -> pexpr TY -> pexpr TY -> linux_memory_order -> action_ TY
  | LinuxRMW : act -> pexpr TY -> pexpr TY -> linux_memory_order -> action_ TY.

Record action (TY : Type) := {
  action_loc : Location_t;
  action_content : action_ TY
}.

Record paction (TY : Type) := {
  paction_polarity : polarity;
  paction_action : action TY
}.

(* Memory operations *)
Inductive memop (TY : Type) : Type :=
  | PtrEq : pexpr TY * pexpr TY -> memop TY
  | PtrNe : pexpr TY * pexpr TY -> memop TY
  | PtrLt : pexpr TY * pexpr TY -> memop TY
  | PtrGt : pexpr TY * pexpr TY -> memop TY
  | PtrLe : pexpr TY * pexpr TY -> memop TY
  | PtrGe : pexpr TY * pexpr TY -> memop TY
  | Ptrdiff : act * pexpr TY * pexpr TY -> memop TY
  | IntFromPtr : act * act * pexpr TY -> memop TY
  | PtrFromInt : act * act * pexpr TY -> memop TY
  | PtrValidForDeref : act * pexpr TY -> memop TY
  | PtrWellAligned : act * pexpr TY -> memop TY
  | PtrArrayShift : pexpr TY * act * pexpr TY -> memop TY
  | PtrMemberShift : Sym_t * Id_t * pexpr TY -> memop TY
  | Memcpy : pexpr TY * pexpr TY * pexpr TY -> memop TY
  | Memcmp : pexpr TY * pexpr TY * pexpr TY -> memop TY
  | Realloc : pexpr TY * pexpr TY * pexpr TY -> memop TY
  | Va_start : pexpr TY * pexpr TY -> memop TY
  | Va_copy : pexpr TY -> memop TY
  | Va_arg : pexpr TY * act -> memop TY
  | Va_end : pexpr TY -> memop TY
  | CopyAllocId : pexpr TY * pexpr TY -> memop TY.

(* Expressions *)
Inductive expr_ (TY : Type) : Type :=
  | Epure : pexpr TY -> expr_ TY
  | Ememop : memop TY -> expr_ TY
  | Eaction : paction TY -> expr_ TY
  | Eskip : expr_ TY
  | Eccall : act * pexpr TY * list (pexpr TY) -> expr_ TY
  | Elet : pattern TY * pexpr TY * expr TY -> expr_ TY
  | Eunseq : list (expr TY) -> expr_ TY
  | Ewseq : pattern TY * expr TY * expr TY -> expr_ TY
  | Esseq : pattern TY * expr TY * expr TY -> expr_ TY
  | Eif : pexpr TY * expr TY * expr TY -> expr_ TY
  | Ebound : expr TY -> expr_ TY
  | End : list (expr TY) -> expr_ TY
  | Erun : Sym_t * list (pexpr TY) -> expr_ TY
  (* Note: CN_progs constructor omitted as it requires additional types *)

with expr (TY : Type) : Type :=
  | Expr : Location_t -> list Annot_t -> TY -> expr_ TY -> expr TY.

(* Global declarations and definitions *)
Inductive globs (TY : Type) : Type :=
  | GlobalDef : Sctypes_t -> expr TY -> globs TY
  | GlobalDecl : Sctypes_t -> globs TY.

(* Arguments list with logical constraints *)
Inductive arguments (i : Type) : Type :=
  | Define : (Sym_t * IndexTerms_t) * Location_t * arguments i -> arguments i
  | Resource : (Sym_t * (Request_t * BaseTypes_t)) * Location_t * arguments i -> arguments i
  | Constraint : LogicalConstraints_t * Location_t * arguments i -> arguments i
  | I : i -> arguments i.

(* Label specification *)
Record parse_ast_label_spec := {
  label_spec : list cn_condition  (* Note: cn_condition needs to be defined *)
}.

(* Label definition *)
Inductive label_def (TY : Type) : Type :=
  | Return : Location_t -> label_def TY
  | Label : Location_t -> 
           arguments (expr TY) ->
           list Annot_t ->
           parse_ast_label_spec ->
           (Location_t * Location_t) -> (* Loop locations *)
           label_def TY.

(* Trusted status *)
Inductive trusted : Type :=
  | Trusted : Location_t -> trusted
  | Checked : trusted.

(* Desugared specification *)
Record desugared_spec := {
  accesses : list (Sym_t * Type); (* simplified from ctype *)
  requires : list cn_condition;
  ensures : list cn_condition
}.

(* Arguments and body *)
Definition args_and_body (TY : Type) := 
  arguments (expr TY * (SymMap.t (label_def TY)) * ReturnTypes_t).

(* Function map declaration *)
Inductive fun_map_decl (TY : Type) : Type :=
  | Proc : Location_t ->
           args_and_body TY ->
           trusted ->
           desugared_spec ->
           fun_map_decl TY
  | ProcDecl : Location_t -> option ArgumentTypes_ft -> fun_map_decl TY.

(* Tag definition *)
Inductive tag_definition : Type :=
  | StructDef : Memory_struct_layout -> tag_definition
  | UnionDef : tag_definition.

(* Function to convert *)
Record function_to_convert := {
  ftc_loc : Location_t;
  c_fun_sym : Sym_t;
  l_fun_sym : Sym_t
}.

(* Datatype *)
Record datatype := {
  dt_loc : Location_t;
  cases : list (Sym_t * list (Id_t * BaseTypes_t))
}.

(* Note: Some types like cn_condition, ReturnTypes_t, ArgumentTypes_ft, 
   Memory_struct_layout will need to be defined or imported *)


