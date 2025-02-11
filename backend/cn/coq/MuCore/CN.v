Require Import String.
Require Import List.
Require Import ZArith.

Require Import BaseTypes.
Require Import Symbol.
Require Import Location.
Require Import IndexTerms.
Require Import Ctype.
Require Import Location.   

(* C-specific kinds *)
Inductive cn_c_kind : Type :=
  | C_kind_var : cn_c_kind
  | C_kind_enum : cn_c_kind.

(* Variable kinds *)
Inductive cn_var_kind : Type :=
  | Var_kind_c : cn_c_kind -> cn_var_kind
  | Var_kind_cn : cn_var_kind.

(* Sign types *)
Inductive sign : Type :=
  | CN_unsigned : sign
  | CN_signed : sign.

(* Base types *)
Inductive cn_base_type (A : Type) : Type :=
  | CN_unit : cn_base_type A
  | CN_bool : cn_base_type A
  | CN_integer : cn_base_type A
  | CN_bits : sign * nat -> cn_base_type A
  | CN_real : cn_base_type A
  | CN_loc : cn_base_type A
  | CN_alloc_id : cn_base_type A
  | CN_struct : A -> cn_base_type A
  | CN_record : list (Symbol.identifier * cn_base_type A) -> cn_base_type A
  | CN_datatype : A -> cn_base_type A
  | CN_map : cn_base_type A * cn_base_type A -> cn_base_type A
  | CN_list : cn_base_type A -> cn_base_type A
  | CN_tuple : list (cn_base_type A) -> cn_base_type A
  | CN_set : cn_base_type A -> cn_base_type A
  | CN_user_type_name : A -> cn_base_type A
  | CN_c_typedef_name : A -> cn_base_type A.

(* Binary operators *)
Inductive cn_binop : Type :=
  | CN_add : cn_binop
  | CN_sub : cn_binop
  | CN_mul : cn_binop
  | CN_div : cn_binop
  | CN_mod : cn_binop
  | CN_equal : cn_binop
  | CN_inequal : cn_binop
  | CN_lt : cn_binop
  | CN_le : cn_binop
  | CN_gt : cn_binop
  | CN_ge : cn_binop
  | CN_or : cn_binop
  | CN_and : cn_binop
  | CN_implies : cn_binop
  | CN_map_get : cn_binop
  | CN_band : cn_binop
  | CN_bor : cn_binop
  | CN_bxor : cn_binop.

(* Constants *)
Inductive cn_const : Type :=
  | CNConst_NULL : cn_const
  | CNConst_integer : Z -> cn_const
  | CNConst_bits : (sign * nat) * Z -> cn_const
  | CNConst_bool : bool -> cn_const
  | CNConst_unit : cn_const.

(* Pattern types *)
Inductive cn_pat_ (A : Type) : Type :=
  | CNPat_sym : A -> cn_pat_ A
  | CNPat_wild : cn_pat_ A
  | CNPat_constructor : A * list (Symbol.identifier * cn_pat A) -> cn_pat_ A

with cn_pat (A : Type) : Type :=
  | CNPat : Location.t -> cn_pat_ A -> cn_pat A.

(* CN expression type *)
Inductive cn_expr_ (A TY : Type) : Type :=
  | CNExpr_const : cn_const -> cn_expr_ A TY
  | CNExpr_var : A -> cn_expr_ A TY 
  | CNExpr_list : list (cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_memberof : cn_expr A TY * Symbol.identifier -> cn_expr_ A TY
  | CNExpr_arrow : cn_expr A TY * Symbol.identifier -> cn_expr_ A TY
  | CNExpr_record : list (Symbol.identifier * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_struct : A * list (Symbol.identifier * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_memberupdates : cn_expr A TY * list (Symbol.identifier * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_arrayindexupdates : cn_expr A TY * list (cn_expr A TY * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_binop : cn_binop * cn_expr A TY * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_sizeof : TY -> cn_expr_ A TY
  | CNExpr_offsetof : A * Symbol.identifier -> cn_expr_ A TY
  | CNExpr_membershift : cn_expr A TY * option A * Symbol.identifier -> cn_expr_ A TY
  | CNExpr_addr : A -> cn_expr_ A TY
  | CNExpr_cast : cn_base_type A * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_array_shift : cn_expr A TY * option TY * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_call : A * list (cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_cons : A * list (Symbol.identifier * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_each : A * cn_base_type A * (Z * Z) * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_let : A * cn_expr A TY * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_match : cn_expr A TY * list (cn_pat A * cn_expr A TY) -> cn_expr_ A TY
  | CNExpr_ite : cn_expr A TY * cn_expr A TY * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_good : TY * cn_expr A TY -> cn_expr_ A TY
  | CNExpr_deref : cn_expr A TY -> cn_expr_ A TY
  | CNExpr_value_of_c_atom : A * cn_c_kind -> cn_expr_ A TY
  | CNExpr_unchanged : cn_expr A TY -> cn_expr_ A TY
  | CNExpr_at_env : cn_expr A TY * string -> cn_expr_ A TY
  | CNExpr_not : cn_expr A TY -> cn_expr_ A TY
  | CNExpr_negate : cn_expr A TY -> cn_expr_ A TY
  | CNExpr_default : cn_base_type A -> cn_expr_ A TY
  | CNExpr_bnot : cn_expr A TY -> cn_expr_ A TY

with cn_expr (A TY : Type) : Type :=
  | CNExpr : Location.t * cn_expr_ A TY -> cn_expr A TY.

(* CN predicate types *)
Inductive cn_pred (A TY : Type) : Type :=
  | CN_owned : option TY -> cn_pred A TY
  | CN_block : option TY -> cn_pred A TY
  | CN_named : A -> cn_pred A TY.

(* CN resource types *)
Inductive cn_resource (A TY : Type) : Type :=
  | CN_pred : Location_t -> cn_pred A TY -> list (cn_expr A TY) -> cn_resource A TY
  | CN_each : A -> cn_base_type A -> cn_expr A TY -> Location_t -> 
              cn_pred A TY -> list (cn_expr A TY) -> cn_resource A TY.

(* CN assertion types *)
Inductive cn_assertion (A TY : Type) : Type :=
  | CN_assert_exp : cn_expr A TY -> cn_assertion A TY
  | CN_assert_qexp : A -> cn_base_type A -> cn_expr A TY -> cn_expr A TY -> cn_assertion A TY.

(* CN condition types *)
Inductive cn_condition (A TY : Type) : Type :=
  | CN_cletResource : Location.t -> A -> cn_resource A TY -> cn_condition A TY
  | CN_cletExpr : Location.t -> A -> cn_expr A TY -> cn_condition A TY
  | CN_cconstr : Location.t -> cn_assertion A TY -> cn_condition A TY.

(* Function specifications *)
Inductive cn_function_spec (A TY : Type) : Type :=
  | CN_accesses : Location.t * list Symbol.identifier -> cn_function_spec A TY
  | CN_requires : Location.t * list (cn_condition A TY) -> cn_function_spec A TY
  | CN_ensures : Location.t * list (cn_condition A TY) -> cn_function_spec A TY
  | CN_trusted : Location.t -> cn_function_spec A TY
  | CN_mk_function : Location.t * A -> cn_function_spec A TY.

(* Loop specifications *)
Inductive cn_loop_spec (A TY : Type) : Type :=
  | CN_inv : Location.t * list (cn_condition A TY) -> cn_loop_spec A TY.

(* Pack/Unpack types *)
Inductive pack_unpack : Type :=
  | Pack : pack_unpack
  | Unpack : pack_unpack.

(* To/From types *)
Inductive to_from : Type :=
  | To : to_from
  | From : to_from.

(* Instantiation types *)
Inductive cn_to_instantiate (A TY : Type) : Type :=
  | I_Function : A -> cn_to_instantiate A TY
  | I_Good : TY -> cn_to_instantiate A TY
  | I_Everything : cn_to_instantiate A TY.

(* Extraction types *)
Inductive cn_to_extract (A TY : Type) : Type :=
  | E_Pred : cn_pred A TY -> cn_to_extract A TY
  | E_Everything : cn_to_extract A TY.

(* Statement types *)
Inductive cn_statement_ (A TY : Type) : Type :=
  | CN_pack_unpack : pack_unpack * cn_pred A TY * list (cn_expr A TY) -> cn_statement_ A TY
  | CN_to_from_bytes : to_from * cn_pred A TY * list (cn_expr A TY) -> cn_statement_ A TY
  | CN_have : cn_assertion A TY -> cn_statement_ A TY
  | CN_instantiate : cn_to_instantiate A TY * cn_expr A TY -> cn_statement_ A TY
  | CN_split_case : cn_assertion A TY -> cn_statement_ A TY
  | CN_extract : list Symbol.identifier * cn_to_extract A TY * cn_expr A TY -> cn_statement_ A TY
  | CN_unfold : A * list (cn_expr A TY) -> cn_statement_ A TY
  | CN_assert_stmt : cn_assertion A TY -> cn_statement_ A TY
  | CN_apply : A * list (cn_expr A TY) -> cn_statement_ A TY
  | CN_inline : list A -> cn_statement_ A TY
  | CN_print : cn_expr A TY -> cn_statement_ A TY
with cn_statement (A TY : Type) := 
  | CN_statement: Location.t -> (cn_statement_ A TY) -> cn_statement A TY.

(* Namespace types *)
Inductive cn_namespace : Type :=
  | CN_predicate : cn_namespace
  | CN_function : cn_namespace
  | CN_lemma : cn_namespace
  | CN_fun_spec : cn_namespace
  | CN_datatype_nm : cn_namespace
  | CN_constructor : cn_namespace
  | CN_vars : cn_namespace
  | CN_oarg : cn_namespace
  | CN_type_nm : cn_namespace.

(* Error types *)
Inductive cn_error : Type :=
  | CNErr_uppercase_function : Symbol.identifier -> cn_error
  | CNErr_lowercase_predicate : Symbol.identifier -> cn_error
  | CNErr_redeclaration : cn_namespace -> cn_error
  | CNErr_unknown_predicate : cn_error
  | CNErr_invalid_tag : cn_error
  | CNErr_unknown_identifier : cn_namespace * Symbol.identifier -> cn_error
  | CNErr_unknown_c_identifier : Symbol.identifier -> cn_error
  | CNErr_missing_oarg : Symbol.t -> cn_error
  | CNErr_general : string -> cn_error
  | CNErr_duplicate_field : Symbol.identifier -> cn_error.

(* Typing error *)
Inductive cn_typing_error : Type :=
  | CNErr_typing_TODO : cn_typing_error. 