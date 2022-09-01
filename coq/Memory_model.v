Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

Require Import ExtLib.Structures.Monad.

Require Import Addr.
Require Import Mem_common.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Module Type Memory (A:VADDR).

  Import A.
  Include Mem_common(A).

  Parameter Symbol_prefix: Set. (* Symbol.prefix *)
  Parameter Symbol_identifier: Set. (* Symbol.identifier *)
  Parameter Symbol_sym: Set. (* Symbol.sym *)
  Parameter Ctype_ctype: Set. (* Ctype.ctype *)
  Parameter Ctype_integerType: Set. (* Ctype.integerType *)
  Parameter derivecap_op: Set. (* Mem_common.derivecap_op *)
  Parameter integer_operator: Set. (* Mem_common.integer_operator *)
  Parameter Ctype_tag_definition: Set. (* Cerb_frontend.Ctype.tag_definition *)
  Parameter floating_operator: Set. (* Mem_common.floating_operator *)
  Parameter Ctype_floatingType: Set. (* Ctype.floatingType *)
  Parameter intrinsics_signature: Set. (* intrinsics_signature *)

  (* Module interface below *)

  Parameter name : string.
  Parameter pointer_value : Set.
  Parameter integer_value : Set.
  Parameter floating_value : Set.
  Parameter mem_value : Set.

  (*
    Parameter mem_iv_constraint : mem_constraint integer_value.
    Parameter cs_module : Constraints (t := mem_iv_constraint).
   *)

  Parameter footprint : Set.
  Parameter check_overlap : footprint -> footprint -> overlap_status.
  Parameter mem_state : Set.
  Parameter initial_mem_state : mem_state.

  Parameter memM: Type -> Type.
  #[local] Declare Instance memM_monad: Monad memM.

  Parameter _return : forall {a : Set}, a -> memM a.
  Parameter bind : forall {a b : Set}, memM a -> (a -> memM b) -> memM b.

  Parameter allocate_object :
    thread_id -> Symbol_prefix ->
    integer_value -> Ctype_ctype -> option mem_value ->
    memM pointer_value.

  Parameter allocate_region :
    thread_id -> Symbol_prefix ->
    integer_value -> integer_value -> memM pointer_value.

  Parameter kill : Location_ocaml_t -> bool -> pointer_value -> memM unit.

  Parameter load :
    Location_ocaml_t -> Ctype_ctype -> pointer_value ->
    memM (footprint * mem_value).

  Parameter store :
    Location_ocaml_t -> Ctype_ctype -> bool -> pointer_value ->
    mem_value -> memM footprint.

  Parameter null_ptrval : Ctype_ctype -> pointer_value.
  Parameter fun_ptrval : Symbol_sym -> pointer_value.
  Parameter concrete_ptrval : Z -> A.t -> pointer_value.

  Parameter case_ptrval :
    forall {a : Set},
      pointer_value -> (unit -> a) -> (option Symbol_sym -> a) ->
      (unit -> a) -> (unit -> a) -> a.

  Parameter case_funsym_opt :
    mem_state -> pointer_value -> option Symbol_sym.

  Parameter eq_ptrval : pointer_value -> pointer_value -> memM bool.
  Parameter ne_ptrval : pointer_value -> pointer_value -> memM bool.
  Parameter lt_ptrval : pointer_value -> pointer_value -> memM bool.
  Parameter gt_ptrval : pointer_value -> pointer_value -> memM bool.
  Parameter le_ptrval : pointer_value -> pointer_value -> memM bool.
  Parameter ge_ptrval : pointer_value -> pointer_value -> memM bool.

  Parameter diff_ptrval :
    Ctype_ctype -> pointer_value -> pointer_value ->
    memM integer_value.

  Parameter update_prefix : Symbol_prefix * mem_value -> memM unit.

  Parameter prefix_of_pointer : pointer_value -> memM (option string).

  Parameter validForDeref_ptrval : Ctype_ctype -> pointer_value -> memM bool.

  Parameter isWellAligned_ptrval : Ctype_ctype -> pointer_value -> memM bool.

  Parameter ptrfromint :
    Location_ocaml_t -> Ctype_integerType ->
    Ctype_ctype -> integer_value -> memM pointer_value.

  Parameter intfromptr :
    Location_ocaml_t -> Ctype_ctype ->
    Ctype_integerType -> pointer_value -> memM integer_value.

  Parameter derive_cap :
    bool -> derivecap_op -> integer_value ->  integer_value -> integer_value.

  Parameter cap_assign_value :
    Location_ocaml_t -> integer_value -> integer_value -> integer_value.

  Parameter ptr_t_int_value : integer_value -> integer_value.

  Parameter null_cap : bool -> integer_value.

  Parameter array_shift_ptrval :
    pointer_value -> Ctype_ctype -> integer_value ->
    pointer_value.

  Parameter member_shift_ptrval :
    pointer_value -> Symbol_sym ->
    Symbol_identifier -> pointer_value.

  Parameter eff_array_shift_ptrval :
    Location_ocaml_t -> pointer_value -> Ctype_ctype ->
    integer_value -> memM pointer_value.

  Parameter eff_member_shift_ptrval :
    Location_ocaml_t -> pointer_value -> Symbol_sym ->
    Symbol_identifier -> memM pointer_value.

  Parameter memcpy :
    pointer_value -> pointer_value -> integer_value -> memM pointer_value.

  Parameter memcmp :
    pointer_value -> pointer_value -> integer_value -> memM integer_value.

  Parameter realloc :
    thread_id -> integer_value -> pointer_value ->
    integer_value -> memM pointer_value.

(* Following could be implemented in OCaml wrapper
  Parameter va_start :
    list (Ctype_ctype * pointer_value) -> memM integer_value.
  Parameter va_copy : integer_value -> memM integer_value.
  Parameter va_arg : integer_value -> Ctype_ctype -> memM pointer_value.
  Parameter va_end : integer_value -> memM unit.
  Parameter va_list :
    Z -> memM (list (Ctype_ctype * pointer_value)).
 *)

  Parameter copy_alloc_id : integer_value -> pointer_value -> memM pointer_value.

  Parameter concurRead_ival :
    Ctype_integerType -> Symbol_sym ->
    integer_value.

  Parameter integer_ival : Z -> integer_value.
  Parameter max_ival : Ctype_integerType -> integer_value.
  Parameter min_ival : Ctype_integerType -> integer_value.
  Parameter op_ival :
    integer_operator -> integer_value ->
    integer_value -> integer_value.

  Parameter offsetof_ival :
    (Symbol_sym -> option Ctype_tag_definition) (* Pmap_map *) ->
    Symbol_sym -> Symbol_identifier ->
    integer_value.

  Parameter sizeof_ival : Ctype_ctype -> integer_value.
  Parameter alignof_ival : Ctype_ctype -> integer_value.
  Parameter bitwise_complement_ival :
    Ctype_integerType -> integer_value -> integer_value.
  Parameter bitwise_and_ival :
    Ctype_integerType -> integer_value -> integer_value ->
    integer_value.
  Parameter bitwise_or_ival :
    Ctype_integerType -> integer_value -> integer_value ->
    integer_value.
  Parameter bitwise_xor_ival :
    Ctype_integerType -> integer_value -> integer_value ->
    integer_value.

  Parameter case_integer_value :
    forall {a : Set},
      integer_value -> (Z -> a) -> (unit -> a) -> a.
  Parameter is_specified_ival : integer_value -> bool.
  Parameter eq_ival : option mem_state -> integer_value -> integer_value -> option bool.
  Parameter lt_ival : option mem_state -> integer_value -> integer_value -> option bool.
  Parameter le_ival : option mem_state -> integer_value -> integer_value -> option bool.
  Parameter eval_integer_value : integer_value -> option Z.
  Parameter zero_fval : floating_value.
  Parameter one_fval : floating_value.
  Parameter str_fval : string -> floating_value.

  (* TODO: see if we can avoid float.
    Parameter case_fval :
      forall {a : Set}, floating_value -> (unit -> a) -> (float -> a) -> a.
   *)

  Parameter op_fval :
    floating_operator -> floating_value ->
    floating_value -> floating_value.

  Parameter eq_fval : floating_value -> floating_value -> bool.
  Parameter lt_fval : floating_value -> floating_value -> bool.
  Parameter le_fval : floating_value -> floating_value -> bool.
  Parameter fvfromint : integer_value -> floating_value.
  Parameter ivfromfloat :
    Ctype_integerType -> floating_value -> integer_value.
  Parameter unspecified_mval : Ctype_ctype -> mem_value.
  Parameter integer_value_mval :
    Ctype_integerType -> integer_value -> mem_value.
  Parameter floating_value_mval :
    Ctype_floatingType -> floating_value -> mem_value.
  Parameter pointer_mval : Ctype_ctype -> pointer_value -> mem_value.
  Parameter array_mval : list mem_value -> mem_value.
  Parameter struct_mval :
    Symbol_sym ->
    list
      (Symbol_identifier * Ctype_ctype * mem_value)
    -> mem_value.
  Parameter union_mval :
    Symbol_sym -> Symbol_identifier ->
    mem_value -> mem_value.

  Parameter case_mem_value :
    forall {a : Set},
      mem_value -> (Ctype_ctype -> a) ->
      (Ctype_integerType -> Symbol_sym -> a) ->
      (Ctype_integerType -> integer_value -> a) ->
      (Ctype_floatingType -> floating_value -> a) ->
      (Ctype_ctype -> pointer_value -> a) ->
      (list mem_value -> a) ->
      (Symbol_sym ->
       list
         (Symbol_identifier * Ctype_ctype * mem_value)
       -> a) ->
      (Symbol_sym -> Symbol_identifier ->
       mem_value -> a) -> a.
  Parameter sequencePoint : memM unit.
  Parameter call_intrinsic :
    Location_ocaml_t -> string -> list mem_value -> memM (option mem_value).
  Parameter get_intrinsic_type_spec :
    string -> option intrinsics_signature.

(*
    pp_pointer_value : option bool -> pointer_value -> PPrint.document.
    pp_integer_value : integer_value -> PPrint.document.
    pp_integer_value_for_core : integer_value -> PPrint.document.
    pp_mem_value : mem_value -> PPrint.document.
    pp_pretty_pointer_value : pointer_value -> PPrint.document.
    pp_pretty_integer_value :
      Cerb_frontend.Boot_printf.formatting -> integer_value -> PPrint.document.
    pp_pretty_mem_value :
      Cerb_frontend.Boot_printf.formatting -> mem_value -> PPrint.document.

    serialise_mem_state : Stdlib.Digest.t -> mem_state -> Json.json.
 *)
End Memory.
