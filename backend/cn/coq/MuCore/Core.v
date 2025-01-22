Require Import Symbol.

Inductive core_object_type : Type :=  (* types for C objects *)
  | OTy_integer : core_object_type
  | OTy_floating : core_object_type
  | OTy_pointer : core_object_type
  | OTy_array : core_object_type -> core_object_type
  | OTy_struct : Symbol.sym -> core_object_type
  | OTy_union : Symbol.sym -> core_object_type
.

Inductive core_base_type : Type :=  (* Core base types *)
  | BTy_unit     : core_base_type  (* unit *)
  | BTy_boolean  : core_base_type  (* boolean *)
  | BTy_ctype    : core_base_type  (* Core type of C type exprs *)
  | BTy_list     : core_base_type -> core_base_type  (* list *)
  | BTy_tuple    : list core_base_type -> core_base_type  (* tuple *)
  | BTy_object   : core_object_type -> core_base_type  (* C object value *)
  | BTy_loaded   : core_object_type -> core_base_type  (* core_object_type or unspecified *)
  | BTy_storable : core_base_type  (* top type for integer/float/pointer/structs (maybe union?). This is only used in the type system *)
.
