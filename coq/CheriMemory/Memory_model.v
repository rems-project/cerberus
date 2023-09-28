Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

Require Import ExtLib.Structures.Monad.

From CheriCaps.Common Require Import Addr Capabilities.

Require Import CoqLocation.
Require Import CoqSymbol.
Require Import CoqMem_common.
Require Import CoqCtype.
Require Import Common.SimpleError.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Module Type Memory (A:PTRADDR) (B:PTRADDR_INTERVAL A) (MC:Mem_common(A)(B)).

  Import A.
  Import MC.

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
  Parameter overlapping : footprint -> footprint -> bool.
  Parameter mem_state : Type.
  Parameter initial_mem_state : mem_state.

  Parameter memM: Type -> Type.
  #[local] Declare Instance memM_monad: Monad memM.

  Parameter allocate_object :
    thread_id -> CoqSymbol.prefix ->
    integer_value -> CoqCtype.ctype -> option mem_value ->
    memM pointer_value.

  Parameter allocate_region :
    thread_id -> CoqSymbol.prefix ->
    integer_value -> integer_value -> memM pointer_value.

  Parameter kill : location_ocaml -> bool -> pointer_value -> memM unit.

  Parameter load :
    location_ocaml -> CoqCtype.ctype -> pointer_value ->
    memM (footprint * mem_value).

  Parameter store :
    location_ocaml -> CoqCtype.ctype -> bool -> pointer_value ->
    mem_value -> memM footprint.

  Parameter null_ptrval : CoqCtype.ctype -> pointer_value.
  Parameter fun_ptrval : CoqSymbol.sym -> serr pointer_value.
  Parameter concrete_ptrval : Z -> A.t -> serr pointer_value.

  (* Parameter case_ptrval :
    forall {A : Set},
      pointer_value -> (unit -> A) -> (option CoqSymbol.sym -> A) ->
      (unit -> A) -> (unit -> A) -> serr A. *)

  Parameter case_funsym_opt :
    mem_state -> pointer_value -> option CoqSymbol.sym.

  Parameter eq_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.
  Parameter ne_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.
  Parameter lt_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.
  Parameter gt_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.
  Parameter le_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.
  Parameter ge_ptrval : location_ocaml -> pointer_value -> pointer_value -> memM bool.

  Parameter diff_ptrval :
    location_ocaml ->
    CoqCtype.ctype -> pointer_value -> pointer_value ->
    memM integer_value.

  Parameter update_prefix : CoqSymbol.prefix * mem_value -> memM unit.

  (* Parameter prefix_of_pointer : pointer_value -> memM (option string). *)

  Parameter validForDeref_ptrval : CoqCtype.ctype -> pointer_value -> memM bool.

  Parameter isWellAligned_ptrval : CoqCtype.ctype -> pointer_value -> memM bool.

  Parameter ptrfromint :
    location_ocaml -> CoqCtype.integerType ->
    CoqCtype.ctype -> integer_value -> memM pointer_value.

  Parameter intfromptr :
    location_ocaml -> CoqCtype.ctype ->
    CoqCtype.integerType -> pointer_value -> memM integer_value.

  Parameter derive_cap :
    bool -> derivecap_op -> integer_value ->  integer_value -> serr integer_value.

  Parameter cap_assign_value :
    location_ocaml -> integer_value -> integer_value -> serr integer_value.

  Parameter ptr_t_int_value : integer_value -> serr integer_value.

  Parameter null_cap : bool -> integer_value.

  Parameter array_shift_ptrval :
    pointer_value -> CoqCtype.ctype -> integer_value ->
    serr pointer_value.

  Parameter member_shift_ptrval :
    pointer_value -> CoqSymbol.sym ->
    CoqSymbol.identifier -> serr pointer_value.

  Parameter eff_array_shift_ptrval :
    location_ocaml -> pointer_value -> CoqCtype.ctype ->
    integer_value -> memM pointer_value.

  Parameter eff_member_shift_ptrval :
    location_ocaml -> pointer_value -> CoqSymbol.sym ->
    CoqSymbol.identifier -> memM pointer_value.

  Parameter memcpy :
    pointer_value -> pointer_value -> integer_value -> memM pointer_value.

  Parameter memcmp :
    pointer_value -> pointer_value -> integer_value -> memM integer_value.

  Parameter realloc :
    location_ocaml ->
    thread_id -> integer_value -> pointer_value ->
    integer_value -> memM pointer_value.

  Parameter va_start :
    list (CoqCtype.ctype * pointer_value) -> memM integer_value.
  Parameter va_copy : integer_value -> memM integer_value.
  Parameter va_arg : integer_value -> CoqCtype.ctype -> memM pointer_value.
  Parameter va_end : integer_value -> memM unit.
  Parameter va_list :
    Z -> memM (list (CoqCtype.ctype * pointer_value)).

  Parameter copy_alloc_id : integer_value -> pointer_value -> memM pointer_value.

  Parameter concurRead_ival :
    CoqCtype.integerType -> CoqSymbol.sym ->
    serr integer_value.

  Parameter integer_ival : Z -> integer_value.
  Parameter max_ival : CoqCtype.integerType -> serr integer_value.
  Parameter min_ival : CoqCtype.integerType -> serr integer_value.
  Parameter op_ival :
    integer_operator -> integer_value ->
    integer_value -> integer_value.

  Parameter offsetof_ival :
    (SymMap.t CoqCtype.tag_definition) ->
    CoqSymbol.sym -> CoqSymbol.identifier ->
    serr integer_value.

  Parameter sizeof_ival : CoqCtype.ctype -> serr integer_value.
  Parameter alignof_ival : CoqCtype.ctype -> serr integer_value.
  Parameter bitwise_complement_ival :
    CoqCtype.integerType -> integer_value -> integer_value.
  Parameter bitwise_and_ival :
    CoqCtype.integerType -> integer_value -> integer_value ->
    integer_value.
  Parameter bitwise_or_ival :
    CoqCtype.integerType -> integer_value -> integer_value ->
    integer_value.
  Parameter bitwise_xor_ival :
    CoqCtype.integerType -> integer_value -> integer_value ->
    integer_value.

  (* Parameter case_integer_value :
    forall {a : Set},
      integer_value -> (Z -> a) -> (unit -> a) -> a. *)

  Parameter is_specified_ival : integer_value -> bool.
  Parameter eq_ival : integer_value -> integer_value -> option bool.
  Parameter lt_ival : integer_value -> integer_value -> option bool.
  Parameter le_ival : integer_value -> integer_value -> option bool.
  Parameter zero_fval : floating_value.
  Parameter one_fval : floating_value.
  Parameter str_fval : string -> serr floating_value.

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


  (** Not every integer value could be converted to float.
   Hence the error return type *)
  Parameter fvfromint : integer_value -> serr floating_value.

  Parameter ivfromfloat :
    CoqCtype.integerType -> floating_value -> serr integer_value.

  Parameter unspecified_mval : CoqCtype.ctype -> mem_value.
  Parameter integer_value_mval :
    CoqCtype.integerType -> integer_value -> mem_value.
  Parameter floating_value_mval :
    CoqCtype.floatingType -> floating_value -> mem_value.
  Parameter pointer_mval : CoqCtype.ctype -> pointer_value -> mem_value.
  Parameter array_mval : list mem_value -> mem_value.
  Parameter struct_mval :
    CoqSymbol.sym ->
    list
      (CoqSymbol.identifier * CoqCtype.ctype * mem_value)
    -> mem_value.
  Parameter union_mval :
    CoqSymbol.sym -> CoqSymbol.identifier ->
    mem_value -> mem_value.

  (* Parameter case_mem_value :
    forall {a : Set},
      mem_value -> (CoqCtype.ctype -> a) ->
      (CoqCtype.integerType -> CoqSymbol.sym -> a) ->
      (CoqCtype.integerType -> integer_value -> a) ->
      (CoqCtype.floatingType -> floating_value -> a) ->
      (CoqCtype.ctype -> pointer_value -> a) ->
      (list mem_value -> a) ->
      (CoqSymbol.sym ->
       list
         (CoqSymbol.identifier * CoqCtype.ctype * mem_value)
       -> a) ->
      (CoqSymbol.sym -> CoqSymbol.identifier ->
       mem_value -> a) -> a. *)

  Parameter sequencePoint : memM unit.
  Parameter call_intrinsic :
    location_ocaml -> string -> list mem_value -> memM (option mem_value).
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

    serialise_mem_state : Stdlib.Digest.t -> mem_state -> Cerb_json.json.
 *)
End Memory.
