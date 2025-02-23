(* Types for memory model used in CN (VIP memory model) 
   This is a simplified version of the memory model used in CN.
   It is based on the VIP memory model, but it is simplified to be used in Coq.
*)

Require Import Coq.NArith.NArith.
Require Import Coq.Floats.PrimFloat.

Require Import Memory.
Require Import Symbol.
Require Import IntegerType.
Require Import Ctype.

Module CNMem.

    (* INTERNAL: allocation_id *)
    Definition allocation_id := N.t.

    (* INTERNAL: provenance *)
    Inductive provenance_t : Type :=
      | Prov_empty : provenance_t
      | Prov_some : allocation_id -> provenance_t.

    (* EXTERNAL *)
    Definition provenance := provenance_t.

    (* INTERNAL: address *)
    Definition address := N.t.

    (* INTERNAL: location *)
    Definition location := (provenance * address)%type.

    (* INTERNAL: pointer_value *)
    Inductive pointer_value_t : Type :=
    | PVnull : pointer_value_t
    | PVloc : location -> pointer_value_t
    | PVfunptr : Symbol.sym -> pointer_value_t.

    (* EXTERNAL *)
    Definition pointer_value := pointer_value_t.

    (* INTERNAL: integer_value *)
    Inductive integer_value_t : Type :=
    | IVloc : location -> integer_value_t
    | IVint : N.t -> integer_value_t.

    (* EXTERNAL *)
    Definition integer_value := integer_value_t.

    (* EXTERNAL *)
    Definition floating_value := float.

    (* INTERNAL: mem_value *)
    Inductive mem_value_t: Type :=
    | MVunspecified : Ctype.ctype -> mem_value_t
    | MVinteger : IntegerType.integerType -> integer_value_t -> mem_value_t
    | MVfloating : Ctype.floatingType -> floating_value -> mem_value_t
    | MVpointer : Ctype.ctype -> pointer_value_t -> mem_value_t
    | MVarray : list mem_value_t -> mem_value_t
    | MVstruct : Symbol.sym -> list (Symbol.identifier * Ctype.ctype * mem_value_t) -> mem_value_t
    | MVunion : Symbol.sym -> Symbol.identifier -> mem_value_t -> mem_value_t.

    (* EXTERNAL *)
    Definition mem_value := mem_value_t.

End CNMem.
