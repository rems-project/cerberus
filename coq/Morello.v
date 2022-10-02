Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Bool.Bool.

Require Import bbv.Word.

From Sail Require  Import Base Impl_base Values Operators_mwords.

Require Import Addr Capabilities Utils CapFns.

Module MorelloAddr <: VADDR.
  Definition t := Z.

  Definition bitwise_complement (n:Z) := n. (* TODO *)

  Definition eqb := Z.eqb.
  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Definition ltb_irref := Z.ltb_irrefl.

End MorelloAddr.

Module MoreloOTYPE <: OTYPE.
  Definition t := Z.
End MoreloOTYPE.

Module MorelloCAP_SEAL_T <: CAP_SEAL_T.
  Inductive cap_seal_t :=
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  (* | Cap_Indirect_SEntry_Pair *) (* "LBP" in Morello. TODO see why unused *)
  | Cap_Sealed (seal:MoreloOTYPE.t).

  Definition t := cap_seal_t.
End MorelloCAP_SEAL_T.

Module MorelloVADDR_INTERVAL <: VADDR_INTERVAL(MorelloAddr).
  Definition t := (MorelloAddr.t * MorelloAddr.t)%type.

  Definition addresses_in_interval intr addr :=
    let '(base,limit) := intr in
    andb (MorelloAddr.leb base addr) (MorelloAddr.ltb addr limit).

  Definition ltb (a b:t):= false. (* TODO *)
End MorelloVADDR_INTERVAL.

Module MorelloPermission <: Permission.

  Record morello_perm_record  :=
    {
      global: bool;
      executive: bool ;

      permits_load: bool;
      permits_store: bool;
      permits_execute: bool ;
      permits_load_cap: bool;
      permits_store_cap: bool;
      permits_store_local_cap: bool;
      permits_seal: bool;
      permits_unseal: bool;
      permits_system_access: bool;

      permits_ccall: bool; (* called "permoit_branch_sealer_pair" in Morello *)

      permit_compartment_id: bool; (* Morello-spefic? *)
      permit_mutable_load : bool; (* Morello-spefic? *)

      (* User[N] *)
      user_perms: list bool;
    }.

  Definition t := morello_perm_record.

  Definition user_perms_len := 4%nat.

  Definition perm_is_global := global.
  Definition perm_is_execute := executive.
  Definition perm_is_ccall := permits_ccall.
  Definition perm_is_load := permits_load.
  Definition perm_is_load_cap := permits_load_cap.
  Definition perm_is_seal := permits_seal.
  Definition perm_is_store := permits_store.
  Definition perm_is_store_cap := permits_store_cap.
  Definition perm_is_store_local_cap := permits_store_local_cap.
  Definition perm_is_system_access := permits_system_access.
  Definition perm_is_unseal := permits_unseal.

  Definition get_user_perms := user_perms.

  Definition TODO_ID (x:t) := x.

  Definition perm_clear_global := TODO_ID.
  Definition perm_clear_execute := TODO_ID.
  Definition perm_clear_ccall := TODO_ID.
  Definition perm_clear_load := TODO_ID.
  Definition perm_clear_load_cap := TODO_ID.
  Definition perm_clear_seal := TODO_ID.
  Definition perm_clear_store := TODO_ID.
  Definition perm_clear_store_cap := TODO_ID.
  Definition perm_clear_store_local_cap := TODO_ID.
  Definition perm_clear_system_access := TODO_ID.
  Definition perm_clear_unseal := TODO_ID.

  Definition perm_and_user_perms (p:t) (np:list bool):= p. (* TODO *)

  Definition perm_p0:t :=
    {|
      global := false ;
      executive := false ;
      permits_load := false ;
      permits_store := false ;
      permits_execute := false ;
      permits_load_cap := false ;
      permits_store_cap := false ;
      permits_store_local_cap := false ;
      permits_seal := false ;
      permits_unseal := false ;
      permits_system_access := false ;
      permits_ccall := false ;
      permit_compartment_id := false ;
      permit_mutable_load := false ;
      user_perms := List.repeat false user_perms_len
    |}.

  Definition perm_alloc:t :=
    {|
      global := false ;
      executive := false ;
      permits_load := true ;
      permits_store := true ;
      permits_execute := false ;
      permits_load_cap := true ;
      permits_store_cap := true ;
      permits_store_local_cap := true ;
      permits_seal := false ;
      permits_unseal := false ;
      permits_system_access := false ;
      permits_ccall := false ;
      permit_compartment_id := false ;
      permit_mutable_load := false ;
      user_perms := List.repeat false user_perms_len
    |}.

  Definition perm_alloc_fun:t :=
    {|
      global := false ;
      executive := false ;
      permits_load := true ;
      permits_store := false ;
      permits_execute := true ;
      permits_load_cap := true ;
      permits_store_cap := false ;
      permits_store_local_cap := false ;
      permits_seal := false ;
      permits_unseal := false ;
      permits_system_access := false ;
      permits_ccall := false ;
      permit_compartment_id := false ;
      permit_mutable_load := false ;
      user_perms := List.repeat false user_perms_len
    |}.

  Definition to_string (p:t) := "TODO"%string.

  (* raw permissoins in numeric format *)
  Definition to_raw (p:t) := Z0. (*  TODO *)

  Definition of_list (l: list bool): option t := None. (* TODO *)

  Definition to_list (p:t): list bool := List.nil. (* TODO *)


End MorelloPermission.


Module MorelloCapability <:
  Capability
    (MorelloAddr)
  (MoreloOTYPE)
  (MorelloCAP_SEAL_T)
  (MorelloVADDR_INTERVAL)
  (MorelloPermission).

  Inductive morello_cap_t :=
    {
      valid : bool;
      value : MorelloAddr.t;
      obj_type : MoreloOTYPE.t;
      bounds : MorelloVADDR_INTERVAL.t;
      flags : list bool;
      perms : MorelloPermission.t
    }.

  Definition with_valid valid (r : morello_cap_t) :=
    Build_morello_cap_t valid r.(value) r.(obj_type) r.(bounds) r.(flags) r.(perms).
  Definition with_value value (r : morello_cap_t) :=
    Build_morello_cap_t r.(valid) value r.(obj_type) r.(bounds) r.(flags) r.(perms).
  Definition with_obj_type obj_type (r : morello_cap_t) :=
    Build_morello_cap_t r.(valid) r.(value) obj_type r.(bounds) r.(flags) r.(perms).
  Definition with_bounds bounds (r : morello_cap_t) :=
    Build_morello_cap_t r.(valid) r.(value) r.(obj_type) bounds r.(flags) r.(perms).
  Definition with_flags flags (r : morello_cap_t) :=
    Build_morello_cap_t r.(valid) r.(value) r.(obj_type) r.(bounds) flags r.(perms).
  Definition with_perms perms (r : morello_cap_t) :=
    Build_morello_cap_t r.(valid) r.(value) r.(obj_type) r.(bounds) r.(flags) perms.

  Definition t := morello_cap_t.

  Definition sizeof_vaddr : nat := 8.

  Definition vaddr_bits : nat := Nat.mul sizeof_vaddr 8%nat.

  Definition min_vaddr : Z := 0.

  Definition max_vaddr : Z := Z.sub (Z.pow 2 (Z.of_nat vaddr_bits)) 1.

  Definition cap_flags_len : nat := 8%nat.

  Definition cap_is_valid (c_value : t) : bool := c_value.(valid).

  Definition cap_get_obj_type (c_value : t)  := c_value.(obj_type).

  Definition cap_get_value (c_value : t)  := c_value.(value).

  Definition cap_get_bounds (c_value : t) := c_value.(bounds).

  Definition cap_get_offset (c_value : t) : Z :=
    Z.sub c_value.(value) (fst c_value.(bounds)).

  Definition cap_SEAL_TYPE_UNSEALED := 0.
  Definition cap_SEAL_TYPE_RB  := 1.
  Definition cap_SEAL_TYPE_LPB := 2.
  Definition cap_SEAL_TYPE_LB  := 3.

  Definition cap_get_seal (c_value : t) : MorelloCAP_SEAL_T.t :=
    let x_value := c_value.(obj_type) in
    if Z.eqb x_value cap_SEAL_TYPE_UNSEALED then
      MorelloCAP_SEAL_T.Cap_Unsealed
    else
      if Z.eqb x_value cap_SEAL_TYPE_RB then
        MorelloCAP_SEAL_T.Cap_SEntry
      else
        if Z.eqb x_value cap_SEAL_TYPE_LPB then
          MorelloCAP_SEAL_T.Cap_Indirect_SEntry
        else
          if Z.eqb x_value cap_SEAL_TYPE_LB then
            MorelloCAP_SEAL_T.Cap_Indirect_SEntry
          else
            MorelloCAP_SEAL_T.Cap_Sealed x_value.

  Definition cap_get_flags (c_value : t) : list bool := c_value.(flags).

  Definition cap_get_perms c_value := c_value.(perms).

  (* helper function to convert [mword] to list of booleans *)
  Definition mword_to_bools {n:Z} (w: mword n) :=
    List.map bool_of_bit (bits_of w).

  Definition flags_from_value_bits (x : mword 64) : list bool :=
    let x := zero_extend x 64 in
    let xl := mword_to_bools x in
    List.skipn (Nat.sub 64 8)%nat xl.

  Definition flags_from_value (v : MorelloAddr.t) : list bool :=
    let w := mword_of_int v (len:= Z.of_nat vaddr_bits) in
    flags_from_value_bits w.

  Definition decode_word (bits : mword 129) : option t :=
    let value' := CapGetValue bits in
    let value := projT1 (uint value') in
    match CapGetBounds bits with
    | Done (base', limit', isExponentValid) =>
        if negb isExponentValid
        then None
        else
          let flags := flags_from_value_bits value' in
          let perms' := CapGetPermissions bits in
          let perms_data := mword_to_bools perms' in
          match MorelloPermission.of_list perms_data with
          | None =>
              None
          | Some perms =>
              let otype := projT1 (uint (CapGetObjectType bits)) in
              Some
                {| valid := CapIsTagSet bits;
                  value := value;
                  obj_type := otype;
                  bounds := (projT1 (uint base'), projT1 (uint limit'));
                  flags := flags;
                  perms := perms |}
          end
    | _ => None
    end.

  Program Definition decode (bytes : list ascii) (tag : bool) : option t :=
    if Nat.eqb (List.length bytes) 16%nat then
      let bytes := List.rev bytes in
      let bits := tag::(bool_bits_of_bytes bytes) in
      let bitsu := List.map bitU_of_bool bits in
      let w := vec_of_bits bitsu in
      decode_word w
    else
      None.
  Next Obligation.
    admit. (* TODO: prove that (lenght (bool_bits_of_bytes)==128)
              and ehence [w] is 129-bit long *)
  Admitted.

  Definition cap_c0 (_: unit) : option t :=
    decode_word (CapNull tt).

  Definition alloc_cap (a_value : MorelloAddr.t) (size : Z) : t :=
    {|
      valid := true;
      value := a_value;
      obj_type := cap_SEAL_TYPE_UNSEALED;
      bounds := (a_value, (Z.add a_value size));
      flags := flags_from_value a_value;
      perms := MorelloPermission.perm_alloc
    |}.

  Definition alloc_fun (a_value : MorelloAddr.t) : t :=
    {|
      valid := true;
      value := a_value;
      obj_type := cap_SEAL_TYPE_RB;
      bounds := (a_value, (Z.succ (Z.succ a_value)));
      flags := flags_from_value a_value;
      perms := MorelloPermission.perm_alloc_fun
    |}.


End MorelloCapability.
