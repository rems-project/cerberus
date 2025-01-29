(* Module Mucore - CN-specific variant of Cerberus Core 
   A more specialized version of Core – this is what CN actually uses. *)

Require Import String.
Require Import List.
Require Import ZArith.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Sym.
Require Import Location.
Require Import Core.
Require Import BaseTypes.
Require Import IndexTerms.
Require Import LogicalConstraints.
Require Import Request.
Require Import ReturnTypes.
Require Import ArgumentTypes.
Require Import Ctype.
Require Import Annot.
Require Import Undefined.
Require Import CN.
Require Import CNProgs.
Require Import SCtypes.
Require Import Id.
Require Import ImplMem.

Module Mem := CNMem.

Inductive linux_memory_order : Type :=
  | Once : linux_memory_order
  | LAcquire : linux_memory_order
  | LRelease : linux_memory_order
  | Rmb : linux_memory_order
  | Wmb : linux_memory_order
  | Mb : linux_memory_order
  | RbDep : linux_memory_order
  | RcuLock : linux_memory_order
  | RcuUnlock : linux_memory_order
  | SyncRcu : linux_memory_order.

(* Structure definitions *)
Record struct_piece : Type := mk_struct_piece {
  offset : Z;
  size : Z;
  member_or_padding : option (Id.t * SCtypes.t)
}.

Record struct_member : Type := mk_struct_member {
  member_offset : Z;
  member_size : Z;
  member : Id.t * SCtypes.t
}.

Definition struct_layout := list struct_piece.

Inductive memory_order : Type :=
  | NA : memory_order        (* Non-atomic *)
  | Seq_cst : memory_order   (* Sequentially consistent *)
  | Relaxed : memory_order   (* Relaxed ordering *)
  | Release : memory_order   (* Release ordering *)
  | Acquire : memory_order   (* Acquire ordering *)
  | Consume : memory_order   (* Consume ordering *)
  | Acq_rel : memory_order.  (* Acquire-Release ordering *)

Inductive polarity : Type :=
  | Pos : polarity  (* Positive polarity *)
  | Neg : polarity. (* Negative polarity *)

Inductive mem_constraint (A : Type) : Type :=
  | MC_empty : mem_constraint A
  | MC_eq : A -> A -> mem_constraint A
  | MC_le : A -> A -> mem_constraint A
  | MC_lt : A -> A -> mem_constraint A
  | MC_in_device : A -> mem_constraint A
  | MC_or : mem_constraint A -> mem_constraint A -> mem_constraint A
  | MC_conj : list (mem_constraint A) -> mem_constraint A
  | MC_not : mem_constraint A -> mem_constraint A.

Definition mem_iv_constraint := mem_constraint Mem.integer_value.

(* Binary operators *)
Inductive binop : Type :=
  | OpAdd : binop    (* Addition *)
  | OpSub : binop    (* Subtraction *)
  | OpMul : binop    (* Multiplication *)
  | OpDiv : binop    (* Division *)
  | OpRem_t : binop  (* Remainder (truncated) *)
  | OpRem_f : binop  (* Remainder (floored) *)
  | OpExp : binop    (* Exponentiation *)
  | OpEq : binop     (* Equality *)
  | OpGt : binop     (* Greater than *)
  | OpLt : binop     (* Less than *)
  | OpGe : binop     (* Greater than or equal *)
  | OpLe : binop     (* Less than or equal *)
  | OpAnd : binop    (* Logical AND *)
  | OpOr : binop.    (* Logical OR *)

(* Integer operators *)
Inductive iop : Type :=
  | IOpAdd : iop     (* Integer addition *)
  | IOpSub : iop     (* Integer subtraction *)
  | IOpMul : iop     (* Integer multiplication *)
  | IOpShl : iop     (* Left shift *)
  | IOpShr : iop.    (* Right shift *)

(* Annotated C type *)
Record act := {
  loc : Location_t;
  annot : list Annot.annot;
  ct : SCtypes.t
}.

Inductive object_value_ (TY : Type) : Type :=
  | OVinteger : Mem.integer_value -> object_value_ TY
  | OVfloating : Mem.floating_value -> object_value_ TY
  | OVpointer : Mem.pointer_value -> object_value_ TY
  | OVarray : list (object_value TY) -> object_value_ TY
  | OVstruct : Sym.t -> list (Symbol.identifier * SCtypes.t * Mem.mem_value) -> object_value_ TY
  | OVunion : Sym.t -> Symbol.identifier -> Mem.mem_value -> object_value_ TY

with object_value (TY : Type) : Type :=
  | OV : TY -> object_value_ TY -> object_value TY.

Inductive value_ (TY : Type) : Type :=
  | Vobject : object_value TY -> value_ TY
  | Vctype : Ctype.ctype -> value_ TY
  | Vfunction_addr : Sym.t -> value_ TY
  | Vunit : value_ TY
  | Vtrue : value_ TY
  | Vfalse : value_ TY
  | Vlist : core_base_type -> list (value TY) -> value_ TY
  | Vtuple : list (value TY) -> value_ TY

with value (TY : Type) : Type :=
  | V : TY -> value_ TY -> value TY.

(* Constructor types *)
Inductive ctor : Type :=
  | Cnil : core_base_type -> ctor
  | Ccons : ctor
  | Ctuple : ctor
  | Carray : ctor.

(* Pattern types *)
Inductive pattern_ (TY : Type) : Type :=
  | CaseBase : option Sym.t * core_base_type -> pattern_ TY
  | CaseCtor : ctor -> list (pattern TY) -> pattern_ TY

with pattern (TY : Type) : Type :=
  | Pattern : Location_t -> list Annot.annot -> TY -> pattern_ TY -> pattern TY.

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
  | Static : SCtypes.t -> m_kill_kind.

(* Pure expressions *)
Inductive pexpr_ (TY: Type) : Type :=
  | PEsym : Sym.t -> pexpr_ TY
  | PEval : value TY -> pexpr_ TY 
  | PEconstrained : list (mem_iv_constraint * pexpr TY) -> pexpr_ TY
  | PEctor : ctor -> list (pexpr TY) -> pexpr_ TY
  | PEbitwise_unop : bw_unop -> pexpr TY -> pexpr_ TY
  | PEbitwise_binop : bw_binop -> pexpr TY -> pexpr TY -> pexpr_ TY
  | Cfvfromint : pexpr TY -> pexpr_ TY
  | Civfromfloat : act -> pexpr TY -> pexpr_ TY
  | PEarray_shift : pexpr TY -> SCtypes.t -> pexpr TY -> pexpr_ TY
  | PEmember_shift : pexpr TY -> Sym.t -> Symbol.identifier -> pexpr_ TY
  | PEnot : pexpr TY -> pexpr_ TY
  | PEop : binop -> pexpr TY -> pexpr TY -> pexpr_ TY
  | PEapply_fun : mu_function -> list (pexpr TY) -> pexpr_ TY
  | PEstruct : Sym.t -> list (Symbol.identifier * pexpr TY) -> pexpr_ TY
  | PEunion : Sym.t -> Symbol.identifier -> pexpr TY -> pexpr_ TY
  | PEcfunction : pexpr TY -> pexpr_ TY
  | PEmemberof : Sym.t -> Symbol.identifier -> pexpr TY -> pexpr_ TY
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
  | Pexpr : Location_t -> list Annot.annot -> TY -> pexpr_ TY -> pexpr TY.

(* Action types *)
Inductive action_ (TY : Type) : Type :=
  | Create : pexpr TY -> act -> Symbol.prefix -> action_ TY
  | CreateReadOnly : pexpr TY -> act -> pexpr TY -> Symbol.prefix -> action_ TY
  | Alloc : pexpr TY -> pexpr TY -> Symbol.prefix -> action_ TY
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
  | PtrMemberShift : Sym.t * Symbol.identifier * pexpr TY -> memop TY
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
  | Erun : Sym.t * list (pexpr TY) -> expr_ TY
  | ECN_progs : 
      list (cn_statement Symbol.t Ctype.ctype) * 
      list CNProgs.t -> 
      expr_ TY

with expr (TY : Type) : Type :=
  | Expr : Location_t -> list Annot.annot -> TY -> expr_ TY -> expr TY.

(* Global declarations and definitions *)
Inductive globs (TY : Type) : Type :=
  | GlobalDef : SCtypes.t -> expr TY -> globs TY
  | GlobalDecl : SCtypes.t -> globs TY.

(* Arguments list with logical constraints *)
Inductive arguments_l (i : Type) : Type :=
  | Define : (Sym.t * IndexTerms.t) * Locations.info * arguments_l i -> arguments_l i
  | Resource : (Sym.t * (Request.t * BaseTypes.t)) *Locations.info * arguments_l i -> arguments_l i
  | Constraint : LogicalConstraints.t * Locations.info * arguments_l i -> arguments_l i
  | I : i -> arguments_l i.

Inductive arguments (i : Type) : Type :=
  | Computational : (Sym.t * BaseTypes.t) * Locations.info * arguments i -> arguments i
  | L : arguments_l i -> arguments i.

(* Label specification *)
Record parse_ast_label_spec := mk_parse_ast_label_spec {
  label_spec : list (cn_condition Symbol.t Ctype.ctype)
}.

(* Label definition *)
Inductive label_def (TY : Type) : Type :=
  | Return : Location_t -> label_def TY
  | Label : Location_t -> 
           arguments (expr TY) ->
           list Annot.annot ->
           parse_ast_label_spec ->
           (Location_t * Location_t) -> (* Loop locations *)
           label_def TY.

(* Trusted status *)
Inductive trusted : Type :=
  | Trusted : Location_t -> trusted
  | Checked : trusted.

(* Desugared specification *)
Record desugared_spec := {
  accesses : list (Sym.t * Ctype.ctype);
  requires : list (cn_condition Symbol.t Ctype.ctype);
  ensures : list (cn_condition Symbol.t Ctype.ctype)  
}.

(* Arguments and body *)
Definition args_and_body (TY : Type) := 
  arguments (expr TY * (SymMap.t (label_def TY)) * ReturnTypes.t).

(* Function map declaration *)
Inductive fun_map_decl (TY : Type) : Type :=
  | Proc : Location_t ->
           args_and_body TY ->
           trusted ->
           desugared_spec ->
           fun_map_decl TY
  | ProcDecl : Location_t -> option ArgumentTypes.ft -> fun_map_decl TY.

(* Tag definition *)
Inductive tag_definition : Type :=
  | StructDef : struct_layout -> tag_definition
  | UnionDef : tag_definition.

(* Function to convert *)
Record function_to_convert := {
  ftc_loc : Location_t;
  c_fun_sym : Sym.t;
  l_fun_sym : Sym.t
}.

(* Datatype *)
Record datatype := {
  dt_loc : Location_t;
  cases : list (Sym.t * list (Symbol.identifier * BaseTypes.t))
}.

