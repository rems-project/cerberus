Require Import Symbol.

Inductive sign : Type :=
  | Signed
  | Unsigned.

Inductive t_gen : Type :=
  | Unit : t_gen
  | Bool : t_gen
  | Integer : t_gen
  | MemByte : t_gen
  | Bits : sign -> nat -> t_gen
  | Real : t_gen
  | Alloc_id : t_gen
  (* | Loc : t_gen -> t_gen  TODO *)
  | CType : t_gen
  | Struct : sym -> t_gen
  | Datatype : sym -> t_gen
  | Record : list (Symbol.identifier * t_gen) -> t_gen
  | Map : t_gen -> t_gen -> t_gen
  | List : t_gen -> t_gen
  | Tuple : list t_gen -> t_gen
  | TSet : t_gen -> t_gen.

Definition t := t_gen.


