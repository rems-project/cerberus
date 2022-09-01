Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Strings.Byte.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Strings.HexString.

Require Import Capabilities.
Require Import Addr.
Require Import Memory_model.
Require Import Mem_common.
Require Import ErrorWithState.
Require Import Undefined.
Require Import Morello.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

Import ListNotations.

Module ZMap := FMapAVL.Make(Z_as_OT).

Module CheriMemory
  (C:Capability(MorelloAddr)
       (MoreloOTYPE)
       (MorelloCAP_SEAL_T)
       (MorelloVADDR_INTERVAL)
       (MorelloPermission)
  ) : Memory(MorelloAddr).

  Include Mem_common(MorelloAddr).

  Definition name := "CHERI memory model".

  Definition symbolic_storage_instance_id : Set := Z.
  Definition storage_instance_id : Set := Z.

  (* Following types need to be defined *)
  Definition Symbol_prefix: Set := unit. (* Symbol.prefix *)
  Definition Symbol_identifier: Set := unit. (* Symbol.identifier *)
  Definition Symbol_sym: Set := unit. (* Symbol.sym *)
  Definition Ctype_ctype: Set := unit. (* Ctype.ctype *)
  Definition Ctype_integerType: Set := unit. (* Ctype.integerType *)
  Definition derivecap_op: Set := unit. (* Mem_common.derivecap_op *)
  Definition integer_operator: Set := unit. (* Mem_common.integer_operator *)
  Definition Ctype_tag_definition: Set := unit. (* Cerb_frontend.Ctype.tag_definition *)
  Definition floating_operator: Set := unit. (* Mem_common.floating_operator *)
  Definition Ctype_floatingType: Set := unit. (* Ctype.floatingType *)
  Definition intrinsics_signature: Set := unit. (* intrinsics_signature *)
  Definition Digest_t: Set := unit. (* OCaml Stdlib.Digest_t *)

  Inductive provenance : Set :=
  | Prov_none : provenance
  | Prov_some : storage_instance_id -> provenance
  | Prov_symbolic : symbolic_storage_instance_id -> provenance
  | Prov_device : provenance.

  Inductive function_pointer : Set :=
  | FP_valid : Symbol_sym -> function_pointer
  | FP_invalid : C.t -> function_pointer.

  Inductive pointer_value_base : Set :=
  | PVfunction : function_pointer -> pointer_value_base
  | PVconcrete : C.t -> pointer_value_base.

  Inductive pointer_value_ind : Set :=
  | PV : provenance -> pointer_value_base -> pointer_value_ind.

  Definition pointer_value := pointer_value_ind.

  Inductive integer_value_ind : Set :=
  | IV : Z -> integer_value_ind
  | IC : bool -> C.t -> integer_value_ind.

  Definition integer_value := integer_value_ind.

  Definition floating_value : Set := float. (* 64 bit *)

  Inductive mem_value_with_err : Set :=
  | MVEunspecified : Ctype_ctype -> mem_value_with_err
  | MVEinteger :
    Ctype_integerType -> integer_value ->
    mem_value_with_err
  | MVEfloating :
    Ctype_floatingType -> floating_value ->
    mem_value_with_err
  | MVEpointer :
    Ctype_ctype -> pointer_value -> mem_value_with_err
  | MVEarray : list mem_value_with_err -> mem_value_with_err
  | MVEstruct :
    Symbol_sym ->
    list  (Symbol_identifier *  Ctype_ctype * mem_value_with_err) ->
    mem_value_with_err
  | MVEunion :
    Symbol_sym ->
    Symbol_identifier -> mem_value_with_err ->
    mem_value_with_err
  | MVErr : mem_error -> mem_value_with_err.

  Inductive mem_value_ind : Set :=
  | MVunspecified : Ctype_ctype -> mem_value_ind
  | MVinteger :
    Ctype_integerType -> integer_value -> mem_value_ind
  | MVfloating :
    Ctype_floatingType -> floating_value -> mem_value_ind
  | MVpointer :
    Ctype_ctype -> pointer_value -> mem_value_ind
  | MVarray : list mem_value_ind -> mem_value_ind
  | MVstruct :
    Symbol_sym ->
    list
      (Symbol_identifier *
         Ctype_ctype * mem_value_ind) -> mem_value_ind
  | MVunion :
    Symbol_sym ->
    Symbol_identifier -> mem_value_ind -> mem_value_ind.

  Definition mem_value := mem_value_ind.

  Inductive MemMonadError :=
  | MemMonadErr: mem_error -> MemMonadError
  | MemMonadUB: (Location_ocaml_t * (list undefined_behaviour)) -> MemMonadError.

  Inductive access_intention : Set :=
  | ReadIntent : access_intention
  | WriteIntent : access_intention
  | CallIntent : access_intention.

  Inductive readonly_status : Set :=
  | IsWritable : readonly_status
  | IsReadOnly_string_literal : readonly_status
  | IsReadOnly : readonly_status.

  Record allocation :=
    {
      prefix : Symbol_prefix;
      base : Z;
      size : Z;
      ty : option Ctype_ctype;
      is_readonly : readonly_status;
      taint : (* `Exposed *) unit + (* `Unexposed *) unit
    }.

  Record AbsByte :=
    {
      prov : provenance;
      copy_offset : option nat;
      value : option byte
    }.

  Record mem_state :=
    {
      next_alloc_id : storage_instance_id;
      next_iota : symbolic_storage_instance_id;
      last_address : Z;
      allocations : ZMap.t allocation;
      iota_map : ZMap.t
                   ((* `Single *) storage_instance_id +
                      (* `Double *) storage_instance_id * storage_instance_id);
      funptrmap : ZMap.t
                    (Digest_t * string * C.t);
      varargs : ZMap.t
                  (Z * list (Ctype_ctype * pointer_value));
      next_varargs_id : Z;
      bytemap : ZMap.t AbsByte;
      captags : ZMap.t bool;
      dead_allocations : list storage_instance_id;
      dynamic_addrs : list Z;
      last_used : option storage_instance_id
    }.

  Definition initial_address := HexString.to_Z "0xFFFFFFFF".

  Definition initial_mem_state : mem_state :=
    {|
      next_alloc_id := Z0;
      next_iota := Z0;
      last_address := initial_address;
      allocations := ZMap.empty allocation;
      iota_map := ZMap.empty (storage_instance_id + storage_instance_id * storage_instance_id);
      funptrmap := ZMap.empty (Digest_t * string * C.t);
      varargs := ZMap.empty (Z * list (Ctype_ctype * pointer_value));
      next_varargs_id := Z0;
      bytemap := ZMap.empty AbsByte;
      captags := ZMap.empty bool;
      dead_allocations := nil;
      dynamic_addrs := nil;
      last_used := None
    |}.


End CheriMemory.
