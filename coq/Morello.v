Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.ZArith.Zdigits.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.HexString.

Require Import StructTact.StructTactics.

Require Import bbv.Word.

From Sail Require  Import Base Impl_base Values Operators_mwords.

Require Import Addr Capabilities Utils CapFns.

Import ListNotations.
Open Scope list_scope.

Module MorelloAddr <: VADDR.
  Definition t := Z. (* but it is always non-negiative *)

  Definition sizeof_vaddr : nat := 8.
  Definition vaddr_bits : nat := Nat.mul sizeof_vaddr 8%nat.

  Definition bitwise_complement (a:Z) :=
    let bits := Z_to_binary vaddr_bits a in
    let bits := Vector.map negb bits in
    binary_value _ bits.

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

  (* convenience constant to be used as size in `mword` *)
  Definition perms_zlen := Z.add (Z.of_nat user_perms_len) 14.

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

  Definition perm_clear_global p :=
    {|
      global                  := false;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_execute p :=
    {|
      global                  := p.(global                  )  ;
      executive               := false;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_ccall p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := false;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_load p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := false;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_load_cap p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := false;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_seal p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := false;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_store p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := false;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_store_cap p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := false;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_store_local_cap p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := false;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_system_access p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := false;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_clear_unseal p :=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := false;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              := p.(user_perms              )  ;
    |}.

  Definition perm_and_user_perms (p:t) (np:list bool):=
    {|
      global                  := p.(global                  )  ;
      executive               := p.(executive               )  ;
      permits_load            := p.(permits_load            )  ;
      permits_store           := p.(permits_store           )  ;
      permits_execute         := p.(permits_execute         )  ;
      permits_load_cap        := p.(permits_load_cap        )  ;
      permits_store_cap       := p.(permits_store_cap       )  ;
      permits_store_local_cap := p.(permits_store_local_cap )  ;
      permits_seal            := p.(permits_seal            )  ;
      permits_unseal          := p.(permits_unseal          )  ;
      permits_system_access   := p.(permits_system_access   )  ;
      permits_ccall           := p.(permits_ccall           )  ;
      permit_compartment_id   := p.(permit_compartment_id   )  ;
      permit_mutable_load     := p.(permit_mutable_load     )  ;
      user_perms              :=
        List.map (fun '(a,b) =>  andb a b) (List.combine np p.(user_perms))
    |}.

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

  (* raw permissoins in numeric format *)
  Definition to_raw (p:t) := Z0. (*  TODO *)

  Definition of_list (l: list bool): option t :=
    if Z.ltb (Z.of_nat (List.length l)) perms_zlen
    then
      None
    else
      let off := Nat.add user_perms_len 2 in
      Some
        {|
          global                  := List.nth 0 l false;
          executive               := List.nth 1 l false;
          user_perms              := List.firstn user_perms_len (List.skipn 2 l);
          permit_mutable_load     := List.nth (Nat.add off 0) l false;
          permit_compartment_id   := List.nth (Nat.add off 1) l false;
          permits_ccall           := List.nth (Nat.add off 2) l false;
          permits_system_access   := List.nth (Nat.add off 3) l false;
          permits_unseal          := List.nth (Nat.add off 4) l false;
          permits_seal            := List.nth (Nat.add off 5) l false;
          permits_store_local_cap := List.nth (Nat.add off 6) l false;
          permits_store_cap       := List.nth (Nat.add off 7) l false;
          permits_load_cap        := List.nth (Nat.add off 8) l false;
          permits_execute         := List.nth (Nat.add off 9) l false;
          permits_store           := List.nth (Nat.add off 10) l false;
          permits_load            := List.nth (Nat.add off 11) l false;
        |}.

  Definition to_list (p_value : t) : list bool :=
    List.app [ p_value.(global); p_value.(executive) ]
      (List.app p_value.(user_perms)
        [
          p_value.(permit_mutable_load);
          p_value.(permit_compartment_id);
          p_value.(permits_ccall);
          p_value.(permits_system_access);
          p_value.(permits_unseal);
          p_value.(permits_seal);
          p_value.(permits_store_local_cap);
          p_value.(permits_store_cap);
          p_value.(permits_load_cap);
          p_value.(permits_execute);
          p_value.(permits_store);
          p_value.(permits_load)
        ]).


  (**  Returns an abbreviated textual representation of permissions
       listing zero or more of the following characters:

       r  LOAD permission
       w  STORE permission
       x  EXECUTE permission
       R  LOAD_CAP permission
       W  STORE_CAP permission
       E  EXECUTIVE permission (Morello only)

   *)
  Definition to_string (p:t) : string :=
    let s (f:bool) l := if f then l else "" in
    s p.(permits_load) "r"
    ++ s p.(permits_store) "w"
    ++ s p.(permits_execute) "x"
    ++ s p.(permits_load_cap) "R"
    ++ s p.(permits_store_cap) "W"
    ++ s p.(executive) "E".

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

  Definition sizeof_vaddr : nat := MorelloAddr.sizeof_vaddr.

  Definition vaddr_bits : nat := MorelloAddr.vaddr_bits.

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
    let '(base', limit', isExponentValid) := CapGetBounds bits in
    if negb isExponentValid
    then None
    else
      let flags := flags_from_value_bits value' in
      let perms' := CapGetPermissions bits in
      let perms_data := mword_to_bools perms' in
      match MorelloPermission.of_list perms_data with
      | None => None
      | Some perms =>
          let otype := projT1 (uint (CapGetObjectType bits)) in
          Some
            {| valid := CapIsTagSet bits;
              value := value;
              obj_type := otype;
              bounds := (projT1 (uint base'), projT1 (uint limit'));
              flags := flags;
              perms := perms |}
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

  Definition cap_c0 (_: unit) : t :=
    {| valid := false;
      value := 0;
      obj_type := 0;
      bounds := (0, 18446744073709551616);
      flags := [false; false; false; false; false; false; false; false];
      perms :=
        {|
          MorelloPermission.global := false;
          MorelloPermission.executive := false ;
          MorelloPermission.permits_load := false;
          MorelloPermission.permits_store := false;
          MorelloPermission.permits_execute := false ;
          MorelloPermission.permits_load_cap := false;
          MorelloPermission.permits_store_cap := false;
          MorelloPermission.permits_store_local_cap := false;
          MorelloPermission.permits_seal := false;
          MorelloPermission.permits_unseal := false;
          MorelloPermission.permits_system_access := false;
          MorelloPermission.permits_ccall := false;
          MorelloPermission.permit_compartment_id := false;
          MorelloPermission.permit_mutable_load := false;

          MorelloPermission.user_perms := [false; false; false; false]
        |}
    |}.

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

  Definition vaddr_in_range (a_value : Z) : bool :=
    Z.geb a_value min_vaddr && Z.leb a_value max_vaddr.

  Definition CapSetPermissins
    (zc: mword 129)
    (zp: mword MorelloPermission.perms_zlen)
    : mword 129
    :=
    update_subrange_vec_dec zc CAP_PERMS_HI_BIT CAP_PERMS_LO_BIT zp.

  Program Definition encode_to_word (isexact : bool) (c : t) : mword 129 :=
    let bits := CapNull tt in
    let bits :=
      CapSetTag bits
        (mword_of_int (len:=64) (if cap_is_valid c then 1 else 0))
    in
    let bits :=
      CapSetObjectType
        bits (mword_of_int (len:=64) (cap_get_obj_type c)) in
    let '(base, limit) := cap_get_bounds c in
    let len := Z.sub limit base in
    let bits := CapSetValue bits (mword_of_int (len:=64) base) in
    let bits := CapSetBounds bits (mword_of_int (len:=65) len) isexact in
    let bits := CapSetValue bits (mword_of_int (len:=64) (cap_get_value c)) in
    let flags := List.map bitU_of_bool (cap_get_flags c) in
    let flags := vec_of_bits flags in
    let flags := zero_extend flags 64 in
    let bits := CapSetFlags bits flags in
    let perms :=
      List.map bitU_of_bool (MorelloPermission.to_list (cap_get_perms c)) in
    let perms := vec_of_bits perms in
    let bits := CapSetPermissins bits perms in
    bits.
  Next Obligation.
    (* TODO: prove that [(MorelloPermission.to_list (cap_get_perms c)) = perms_len] *)
  Admitted.

  Definition cap_vaddr_representable (c : t) (a : Z) : bool
    :=
    vaddr_in_range a &&
      CapIsRepresentable (encode_to_word true c) (mword_of_int (len:=64) a).

  Definition cap_bounds_representable_exactly
    (c : t) (intr : MorelloVADDR_INTERVAL.t) : bool
    :=
    let '(base, limit) := intr in
    let bits := encode_to_word true c in
    let len := Z.sub limit base in
    let base' := mword_of_int (len:=64) base in
    let len' := mword_of_int (len:=65) len in
    let bits := CapSetValue bits base' in
    let bits := CapSetBounds bits len' true in
    CapIsTagSet bits.

  Definition cap_invalidate (c : t) : t := with_valid false c.

  Definition is_sealed (c : t) : bool :=
    match cap_get_seal c with
    | MorelloCAP_SEAL_T.Cap_Unsealed => false
    | _ => true
    end.

  Definition invalidate_if_sealded (c_value : t) : t :=
    if is_sealed c_value then
      cap_invalidate c_value
    else
      c_value.

  Definition cap_set_value (c_value : t) (cv : MorelloAddr.t) : t :=
    if cap_vaddr_representable c_value cv then
      invalidate_if_sealded
        (with_flags (flags_from_value cv) (with_value cv c_value))
    else
      cap_invalidate (with_value cv c_value).

  Definition cap_narrow_bounds (c : t) (bounds : Z * Z) : t :=
    let '(a0, a1) := bounds in
    (* TODO(CHERI): this is placeholder representation. Due to representability constraints bounds may not end up exact as passed *)
    (* assert vaddr_in_range a0 && vaddr_in_range a1 *)
    invalidate_if_sealded (with_bounds (a0, a1) c).

  Definition cap_narrow_bounds_exact (c : t) (bounds : Z * Z)  : t :=
    let '(a0, a1) := bounds in
    (* assert vaddr_in_range a0 && vaddr_in_range a1 *)
    invalidate_if_sealded c.

  Definition cap_narrow_perms (c : t) (p : MorelloPermission.t) : t :=
    let l0 := MorelloPermission.to_list c.(perms) in
    let l1 := MorelloPermission.to_list p in
    let l := List.map (fun '(a,b) =>  andb a b) (List.combine l0 l1) in
    match MorelloPermission.of_list l with
    | Some p => invalidate_if_sealded (with_perms p c)
    | None => c (* impossible case *)
    end.

  Definition cap_seal (c : t) (k : t) : t := cap_set_value c (cap_get_value k).

  Definition cap_seal_entry (c : t) : t := c. (* TODO: looks like it is not implemented yet *)

  Definition cap_seal_indirect_entry (c : t) : t := c. (* TODO: looks like it is not implemented yet *)

  Definition cap_seal_indirect_entry_pair (c : t) : t := c. (* TODO: looks like it is not implemented yet *)

  Definition cap_set_flags (c : t) (f : list bool) : t :=
    invalidate_if_sealded (with_flags f c).

  Definition cap_unseal (c : t) (k : t) : t :=
    with_obj_type cap_SEAL_TYPE_UNSEALED c. (* TODO: looks like it is not implemented yet *)


  (* Internal helper function to conver between Sail bytes ([memory_byte])
     and Cerberus bytes ([ascii]). *)
  Definition memory_byte_to_ascii (b:memory_byte) : option ascii :=
    match List.map bool_of_bit b with
    | [a1;a2;a3;a4;a5;a6;a7;a8] => Some (Ascii a8 a7 a6 a5 a4 a3 a2 a1)
    | _ => None
    end.

  Program Definition encode (isexact : bool) (c : t) : option ((list ascii) * bool) :=
    let w := encode_to_word isexact c in
    let tag := CapIsTagSet w in
    (* strip tag bit *)
    let bits := bits_of w in
    let w1 := vec_of_bits (List.tail bits) in
    match mem_bytes_of_bits w1 with
    | Some bytes =>
        match try_map memory_byte_to_ascii bytes with
        | Some chars => Some (chars, tag)
        | None => None
        end
    | None => None
    end.

  Definition representable_alignment_mask (len: Z) : Z :=
    let len' := mword_of_int (len:=Z.of_nat vaddr_bits) len in
    let mask := CapGetRepresentableMask len' in
    uwordToZ mask.

  Definition representable_length (len : Z) : Z :=
    let mask := representable_alignment_mask len in
    let nmask := MorelloAddr.bitwise_complement mask in
    Z.land (Z.add len nmask) mask.

  Definition eqb (a b : t) : bool :=
    eq_vec (encode_to_word true a) (encode_to_word true b).

  Definition value_compare (x y : t) : comparison :=
    Z.compare x.(value) y.(value).

  (* TODO: this implmenetation seems to be incomplete. Must compare
     all other fields. One idea is to convert both arguments to bit
     vectors and compare them. This would work if the ordering imposed
     by this function only used when indexing hash maps with
     capabilities as keys.

     If used for something else we need to see if this ordering is
     compatible with one imposed by [value_compare]. E.g.  *)
  Definition exact_compare (x y : t) : comparison :=
    match Bool.compare x.(valid) y.(valid) with
    | Eq => value_compare x y
    | Lt => Lt
    | Gt => Gt
    end.

  Definition cap_is_null_derived (c : t) : bool :=
    let a := cap_get_value c in
    let c0 := cap_c0 tt in
    let c' := cap_set_value c0 a in
    eqb c c'.

  Lemma eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.
  Proof.
    (* could not be proven under current definition of eqb! *)
  Admitted.

  Lemma eqb_value_compare: forall a b, eqb a b = true -> value_compare a b = Eq.
  Proof.
    (* could not be proven under current definition of eqb! *)
  Admitted.

  Definition is_sentry (c : t) : bool :=
    match cap_get_seal c with
    | MorelloCAP_SEAL_T.Cap_SEntry => true
    | _ => false
    end.

  Definition flags_as_str (c:t): string :=
    let attrs :=
      let a (f:bool) s l := if f then s::l else l in
      a (negb c.(valid)) "invald"
        (a (is_sentry c) "sentry"
           (a ((negb (is_sentry c)) && is_sealed c) "sealed" []))
    in
    if Nat.eqb (List.length attrs) 0%nat then ""
    else " (" ++ String.concat "," attrs ++ ")".

  Definition to_string (c:t) : string :=
    let vstring x := HexString.of_Z x in
    if cap_is_null_derived c then
      vstring c.(value)
    else
      let (b0,b1) := c.(bounds) in
      (vstring c.(value)) ++ " " ++
        "["++ (MorelloPermission.to_string c.(perms)) ++ "," ++
        (vstring b0) ++ "-" ++
        (vstring b1) ++ "]" ++
        (flags_as_str c).

  (* Not implemented in Coq but in extracted code implementation will
     be mapped to OCaml version *)
  Definition strfcap (formats : string) (capability : t) : option string :=  None.

End MorelloCapability.
