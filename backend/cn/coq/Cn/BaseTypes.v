Require Import Cerberus.Symbol.
Require Import Id.

Inductive sign : Type :=
  | Signed
  | Unsigned.

Inductive t_gen (A:Type) : Type :=
  | Unit : t_gen A  
  | Bool : t_gen A
  | Integer : t_gen A
  | MemByte : t_gen A
  | Bits : sign -> nat -> t_gen A
  | Real : t_gen A
  | Alloc_id : t_gen A
  | Loc : A -> t_gen A
  | CType : t_gen A
  | Struct : Symbol.t -> t_gen A
  | Datatype : Symbol.t -> t_gen A
  | Record : list (Symbol.identifier * t_gen A) -> t_gen A
  | Map : t_gen A -> t_gen A -> t_gen A
  | List : t_gen A -> t_gen A
  | Tuple : list (t_gen A) -> t_gen A
  | TSet : t_gen A -> t_gen A.


Definition member_types_gen (A:Type) := list (Id.t * t_gen A).

Module Datatype.
  Record info (A : Type) := mk_info {
    constrs : list Symbol.t;
    all_params : member_types_gen A
  }.

  Record constr_info (A : Type) := mk_constr_info {
    params : member_types_gen A;
    datatype_tag : Symbol.t
  }.
End Datatype.

Definition t := t_gen unit.

Definition dt_info := Datatype.info unit.
Definition constr_info := Datatype.constr_info unit.
