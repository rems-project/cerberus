(* Module Mucore - CN-specific variant of Cerberus Core 
   A more specialized version of Core – this is what CN actually uses. *)

Require Import String.
Require Import List.
Require Import ZArith.

Require Import MuCore.CerbTypes.

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


(* Annotated C type *)
Record act := {
  loc : Locations_t;
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
  | Pattern : Locations_t -> list Annot_t -> TY -> pattern_ TY -> pattern TY.

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
  | PEundef : Locations_t -> undefined_behaviour -> pexpr_ TY
  | PEerror : string -> pexpr TY -> pexpr_ TY
  | PElet : pattern TY -> pexpr TY -> pexpr TY -> pexpr_ TY
  | PEif : pexpr TY -> pexpr TY -> pexpr TY -> pexpr_ TY

with pexpr (TY: Type) : Type :=
  | Pexpr : Locations_t -> list Annot_t -> TY -> pexpr_ TY -> pexpr TY.