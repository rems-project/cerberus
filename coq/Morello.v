Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Bool.Bool.

Require Import Addr.
Require Import Capabilities.

Module MorelloAddr: VADDR.
  Definition t := Z.

  Definition bitwise_complement (n:Z) := n. (* TODO *)

  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Definition ltb_irref := Z.ltb_irrefl.

  Definition of_Z (x:Z) :t := x.
  Definition to_Z (x:t): Z := x.

End MorelloAddr.

Module MoreloOTYPE : OTYPE.
  Definition t := Z.
End MoreloOTYPE.

Module MorelloCAP_SEAL_T : CAP_SEAL_T.
  Definition t := Z.
End MorelloCAP_SEAL_T.

Module MorelloVADDR_INTERVAL : VADDR_INTERVAL(MorelloAddr).
  Definition t := (MorelloAddr.t * MorelloAddr.t)%type.

  Definition addresses_in_interval intr addr :=
    let '(base,limit) := intr in
    andb (MorelloAddr.leb base addr) (MorelloAddr.ltb addr limit).

  Definition ltb (a b:t):= false. (* TODO *)
End MorelloVADDR_INTERVAL.

Module MorelloPermission : Permission.

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

  Definition user_perms_len := 4.

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
  Definition to_raw (p:t) := N0. (*  TODO *)

  Definition of_list (l: list bool): option t := None. (* TODO *)

  Definition to_list (p:t): list bool := List.nil. (* TODO *)


End MorelloPermission.

