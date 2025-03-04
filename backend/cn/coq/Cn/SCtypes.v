Require Import Cerberus.Symbol.
Require Import Cerberus.IntegerType.
Require Import Cerberus.Ctype.
(* Qualifiers *)
Definition qualifiers := Ctype.qualifiers.

(* C types *)
Inductive ctype : Type :=
  | Void : ctype
  | Integer : integerType -> ctype
  | Array : ctype * option nat -> ctype
  | Pointer : ctype -> ctype
  | Struct : sym -> ctype
  | SCFunction : (qualifiers * ctype) * (list (ctype * bool)) * bool -> ctype.

Definition t := ctype.

Inductive is_struct : t -> Prop :=
  | is_struct_struct : forall s, is_struct (Struct s).

Inductive is_function : t -> Prop :=
  | is_function_function : forall q args ret, is_function (SCFunction (q, args, ret)).


(* C concrete signature *)
Record c_concrete_sig := mk_c_concrete_sig {
  sig_return_ty : Ctype.ctype;
  sig_arg_tys : list Ctype.ctype;
  sig_variadic : bool;
  sig_has_proto : bool
}.