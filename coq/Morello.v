Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.Zdigits.

(* From stdpp Require Import base. *)
From stdpp.unstable Require Import bitvector. 
(*From Cerberus.stdpp_MC.stdpp_unstable Require Import bitvector.*)
(*From Cerberus.stdpp.MC.stdpp.unstable Require Import bitvector. *)
Require Import Sail.Values.
Require Import Sail.Operators_mwords.
Require Import CapFns.

Require Import Capabilities.
Require Import Addr.


(* Notations and their definitions*)

(* Notation "x =? y" := (bool_decide (x = y)) (at level 70, no associativity) . *)
Definition eq {n} (v1:bv n) (v2:bv n) : bool :=
    v1.(bv_unsigned) =? v2.(bv_unsigned).
Notation "x =? y" := (eq x y) (at level 70, no associativity).
Definition lt {n} (v1:bv n) (v2:bv n) : bool :=
    v1.(bv_unsigned) <? v2.(bv_unsigned).
Notation "x <? y" := (lt x y) (at level 70, no associativity).
Notation "x <=? y" := ((x <? y) || (x =? y)).
Notation "x >? y" := (y <? x).

Notation "(<@{ A } )" := (@lt A) (only parsing) : stdpp_scope.
Notation LtDecision A := (RelDecision (<@{A})).

Definition eqb_ADDR (n m : bv 64) : bool := (n =? m)%stdpp.
Definition ltb_ADDR (n m : bv 64) : bool := (n.(bv_unsigned) <? m.(bv_unsigned))%Z.
Definition lte_ADDR (n m : bv 64) : bool := eqb_ADDR n m || ltb_ADDR n m.
Definition ltb_ADDR_irrefl (n : bv 64) := Z.ltb_irrefl n.(bv_unsigned).

(** Utility convertors **)

Definition bv_to_mword {n} (b : bv n) : mword (Z.of_N n) :=
  mword_of_int (b.(bv_unsigned)).
Definition bv_to_Z_unsigned {n} (v : bv n) : Z := v.(bv_unsigned).
Definition bv_to_bv {n} {m : N} (v : bv n) : (bv m) :=
  Z_to_bv m (bv_to_Z_unsigned v).
Definition bv_to_list_bool {n} (v : bv n) : list bool := bv_to_bits v. 

Definition mword_to_Z_unsigned {n} (m : mword n) : Z := int_of_mword false m.
Definition mword_to_N {n} (m : mword n) : N := Z.to_N (int_of_mword false m).
Definition mword_to_bv {n} (m : mword n) : bv (Z.to_N n) :=
  Z_to_bv (Z.to_N n) (mword_to_Z_unsigned m). 

Definition mword_to_bv_2 {z:Z} {n:N} (m : mword z)  : bv n :=
  let x : Z := mword_to_Z_unsigned m in 
  Z_to_bv n x.

  Definition mword_to_list_bool {n} (w : mword n) : list bool := 
  bitlistFromWord (get_word w). 

Definition N_to_mword (m n : N) : mword (Z.of_N m) := 
  mword_of_int (Z.of_N n).
Program Definition list_bool_to_bv (l : list bool) : bv (N.of_nat (List.length l)) := 
  @mword_to_bv (Z.of_nat (List.length l)) (of_bools (List.rev l)).
 Next Obligation. intros. unfold Z.of_nat. destruct (length l). 
 {reflexivity. } {reflexivity. } Defined.  
Definition N_to_nat (n:N) : nat := (Z.to_nat (Z.of_N n)).

Module tests_convertors.
  Example converters_sound_1 : Z_to_bv 3 5 = mword_to_bv (bv_to_mword (Z_to_bv 3 5)).
  Proof. reflexivity. Qed. 
  Example converters_sound_2 : Z_to_bv 11 1000 = mword_to_bv (bv_to_mword (Z_to_bv 11 1000)).
  Proof. reflexivity. Qed. 
  Example converters_sound_3 : N_to_mword 12 2049 = bv_to_mword (mword_to_bv (N_to_mword 12 2049)).
  Proof. reflexivity. Qed. 
  Definition max_value : N := 680564733841876926926749214863536422911. (* 2^129 - 1 *)
  Example converters_sound_4 : N_to_mword 129 max_value = bv_to_mword (mword_to_bv (N_to_mword 129 max_value)).
  Proof. reflexivity. Qed. 
  Example converters_sound_5 : Z_to_bv 129 (Z.of_N max_value) = mword_to_bv (bv_to_mword (Z_to_bv 129 (Z.of_N max_value))).
  Proof. reflexivity. Qed.
End tests_convertors. 

Module PermissionsBV <: Permission.
  Definition len:N := 18. (* CAP_PERMS_NUM_BITS = 16 bits of actual perms + 2 bits for Executive and Global. *)
  Definition t := bv len. 
  
  Definition to_Z (perms:t) : Z := bv_to_Z_unsigned perms.
  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Program Definition of_list_bool (l:list bool)
  `{(N.of_nat (List.length l) = len)%N} : t :=
    list_bool_to_bv l.
  Next Obligation. intros. apply H. Defined.

  Definition user_perms_len:nat := 4.

  Variant perm := Load_perm | Store_perm | Execute_perm | LoadCap_perm | StoreCap_perm | StoreLocalCap_perm | Seal_perm | Unseal_perm
  | System_perm | BranchSealedPair_perm | CompartmentID_perm | MutableLoad_perm | User1_perm | User2_perm | User3_perm | User4_perm | Executive_perm | Global_perm.

  Definition has_perm (permissions:t) : _ -> bool :=
    let perms : (mword 64) := zero_extend (bv_to_mword permissions) 64 in 
    fun perm => CapPermsInclude perms perm.

  Definition has_global_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_GLOBAL.
  Definition has_executive_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_EXECUTIVE.
  Definition has_execute_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_EXECUTE.
  Definition has_load_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_LOAD.
  Definition has_load_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_LOAD_CAP.
  Definition has_seal_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_SEAL.
  Definition has_store_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE.
  Definition has_store_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE_CAP.
  Definition has_store_local_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE_LOCAL.
  Definition has_system_access_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_SYSTEM.
  Definition has_unseal_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_UNSEAL.
  Definition has_user1_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER1.
  Definition has_user2_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER2.
  Definition has_user3_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER3.
  Definition has_user4_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER4.
  Definition has_compartmentID_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_COMPARTMENT_ID.
  Definition has_branch_sealed_pair_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_BRANCH_SEALED_PAIR.
  Definition has_ccall_perm (permissions:t) : bool := 
    has_branch_sealed_pair_perm permissions.
  Definition has_mutable_load_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_MUTABLE_LOAD.
          
  Definition get_user_perms (permissions:t) : list bool := 
    [ has_user1_perm permissions; has_user2_perm permissions; 
      has_user3_perm permissions; has_user4_perm permissions ]. 

  Definition make_permissions (perms: list perm) : list bool :=  
    let isLoad_perm : (perm -> bool) := fun p => match p with Load_perm => true | _ => false end in 
    let isStore_perm : (perm -> bool) := fun p => match p with Store_perm => true | _ => false end in 
    let isExecute_perm : (perm -> bool) := fun p => match p with Execute_perm => true | _ => false end in 
    let isLoadCap_perm : (perm -> bool) := fun p => match p with LoadCap_perm => true | _ => false end in 
    let isStoreCap_perm : (perm -> bool) := fun p => match p with StoreCap_perm => true | _ => false end in 
    let isStoreLocalCap_perm : (perm -> bool) := fun p => match p with StoreLocalCap_perm => true | _ => false end in 
    let isSeal_perm : (perm -> bool) := fun p => match p with Seal_perm => true | _ => false end in 
    let isUnseal_perm : (perm -> bool) := fun p => match p with Unseal_perm => true | _ => false end in 
    let isSystem_perm : (perm -> bool) := fun p => match p with System_perm => true | _ => false end in 
    let isBranchSealedPair_perm : (perm -> bool) := fun p => match p with BranchSealedPair_perm => true | _ => false end in 
    let isCompartmentID_perm : (perm -> bool) := fun p => match p with CompartmentID_perm => true | _ => false end in 
    let isMutableLoad_perm : (perm -> bool) := fun p => match p with MutableLoad_perm => true | _ => false end in 
    let isUser1_perm : (perm -> bool) := fun p => match p with User1_perm => true | _ => false end in 
    let isUser2_perm : (perm -> bool) := fun p => match p with User2_perm => true | _ => false end in 
    let isUser3_perm : (perm -> bool) := fun p => match p with User3_perm => true | _ => false end in 
    let isUser4_perm : (perm -> bool) := fun p => match p with User4_perm => true | _ => false end in 
    let isExecutive_perm : (perm -> bool) := fun p => match p with Executive_perm => true | _ => false end in 
    let isGlobal_perm : (perm -> bool) := fun p => match p with Global_perm => true | _ => false end in 
      [ existsb (isGlobal_perm) perms;           existsb (isExecutive_perm) perms; 
        existsb (isUser1_perm) perms;            existsb (isUser2_perm) perms;  
        existsb (isUser3_perm) perms;            existsb (isUser4_perm) perms;   
        existsb (isMutableLoad_perm) perms;      existsb (isCompartmentID_perm) perms; 
        existsb (isBranchSealedPair_perm) perms; existsb (isSystem_perm) perms;    
        existsb (isUnseal_perm) perms;           existsb (isSeal_perm) perms;     
        existsb (isStoreLocalCap_perm) perms;    existsb (isStoreCap_perm) perms; 
        existsb (isLoadCap_perm) perms;          existsb (isExecute_perm) perms;  
        existsb (isStore_perm) perms;            existsb (isLoad_perm) perms  ].

  Program Definition perm_and_user_perms (perms:t) (user_perms:list bool) : t := 
    let user_perm_4 := (nth 3 user_perms false) && (has_user4_perm perms) in   
    let user_perm_3 := (nth 2 user_perms false) && (has_user3_perm perms) in 
    let user_perm_2 := (nth 1 user_perms false) && (has_user2_perm perms) in 
    let user_perm_1 := (nth 0 user_perms false) && (has_user1_perm perms) in 
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; 
    user_perm_1; user_perm_2; user_perm_3; user_perm_4; has_mutable_load_perm perms;
    has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms;
    has_unseal_perm perms; has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms;
    has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms; has_load_perm perms ] _.
   Next Obligation. reflexivity. Defined.
      
  Program Definition perm_p0 : t := 
    @of_list_bool (make_permissions []) _.
   Next Obligation. reflexivity. Defined.

  Program Definition perm_Universal : t := 
    @of_list_bool (make_permissions [ Global_perm; Executive_perm; User1_perm; User2_perm; 
    User3_perm; User4_perm; MutableLoad_perm; CompartmentID_perm; BranchSealedPair_perm; 
    System_perm; Unseal_perm; Seal_perm; StoreLocalCap_perm; StoreCap_perm; LoadCap_perm; 
    Execute_perm; Store_perm; Load_perm ]) _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_alloc : t :=
    @of_list_bool (make_permissions [ Load_perm; Store_perm; LoadCap_perm; StoreCap_perm; StoreLocalCap_perm ]) _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_alloc_fun : t := 
    @of_list_bool (make_permissions [ Load_perm; Execute_perm; LoadCap_perm ]) _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_global (perms:t) : t :=
    @of_list_bool [ false; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_executive (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; false; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
    
  Program Definition perm_clear_execute (perms:t) : t :=
   @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
   has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
   has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; false; has_store_perm perms;
   has_load_perm perms ] _.
   Next Obligation. reflexivity. Defined.
 
  Program Definition perm_clear_load (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    false ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_load_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; false; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_seal (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    false; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_store (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; false;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_store_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; false; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_store_local_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; false; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_system_access (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; false; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_unseal (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; false;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_branch_sealed_pair (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; false; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
  Program Definition perm_clear_ccall (perms:t) : t := 
    perm_clear_branch_sealed_pair perms.  
  Program Definition perm_clear_mutable_load (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    false; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_compartment_ID (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; false; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user1 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; false; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms;  
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.    

  Program Definition perm_clear_user2 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; false; has_user3_perm perms; has_user4_perm perms;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user3 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; false; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user4 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; false;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  
  
  Definition to_string (perms:t) : string :=
      let s (f:bool) l := if f then l else "" in
      s (has_load_perm perms) "r"
      ++ s (has_store_perm perms) "w"
      ++ s (has_execute_perm perms) "x"
      ++ s (has_load_cap_perm perms) "R"
      ++ s (has_store_cap_perm perms) "W"
      ++ s (has_executive_perm perms) "E".

  Definition to_string_hex (perms:t) : string :=      
    String.hex_string_of_int (bv_to_Z_unsigned perms). 

  Definition to_raw (perms:t) : Z := bv_to_Z_unsigned perms.

  Definition of_list (l : list bool) : option t := 
    if ((List.length l) =? (N_to_nat len))%nat then
      Some (@mword_to_bv (Z.of_N len) (of_bools (List.rev l))) 
    else None.
  
  Definition to_list (perms:t) : list bool := 
    bv_to_list_bool perms.
  
End PermissionsBV.


Module ValueBV <: VADDR.
  Definition len:N := 64.
  Definition t := bv len.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Definition to_Z (v:t) : Z := bv_to_Z_unsigned v.

  Definition bitwise_complement (a:Z) : Z :=
    let bits := Z_to_binary (N_to_nat len) a in
    let bits := Vector.map negb bits in
    binary_value _ bits.

  Definition eqb (v1:t) (v2:t) : bool := v1 =? v2.
  Definition ltb (v1:t) (v2:t) : bool := v1 <? v2.
  Definition leb (v1:t) (v2:t) : bool := v1 <=? v2.
  
  Definition ltb_irref: forall a:t, ltb a a = false.
  Proof. intros. unfold ltb. unfold lt. rewrite Z.ltb_irrefl. reflexivity. Qed. 
  
End ValueBV.


Module ObjTypeBV <: OTYPE.
  Definition len:N := 64.
  Definition t := bv len.  (* ObtTypes are effectively 15-bit values,
  but the ASL extracts this field from a cap as a 64-bit word, 
  possibly to match the size of the objTypes stored in sealing caps *)

  (* Definition CAP_OTYPE_LO_BIT:N := 95.
  Definition CAP_OTYPE_HI_BIT:N := 109.
  Definition CAP_OTYPE_NUM_BITS:N := 15. *)
  Definition CAP_MAX_OBJECT_TYPE:N := 32767.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Definition to_Z (o:t) : Z := bv_to_Z_unsigned o.
End ObjTypeBV.


Module SealType <: CAP_SEAL_T. 
  Inductive cap_seal_t :=
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  | Cap_Indirect_SEntry_Pair (* "LPB" in Morello. TODO see why unused *)
  | Cap_Sealed (seal : ObjTypeBV.t).
  
  Definition t := cap_seal_t. 

  Definition get_seal_ot (seal:t) : ObjTypeBV.t :=
    match seal with 
      Cap_Unsealed => ObjTypeBV.of_Z 0
    | Cap_SEntry => ObjTypeBV.of_Z 1
    | Cap_Indirect_SEntry => ObjTypeBV.of_Z 3
    | Cap_Indirect_SEntry_Pair => ObjTypeBV.of_Z 2
    | Cap_Sealed seal => seal
    end.

  Definition sealed_entry_ot := get_seal_ot Cap_SEntry.
  Definition sealed_indirect_entry_ot := get_seal_ot Cap_Indirect_SEntry.
  Definition sealed_indirect_entry_pair_ot := get_seal_ot Cap_Indirect_SEntry_Pair.

End SealType.


Module BoundsBV <: VADDR_INTERVAL(ValueBV).
  (* Definition t := bv 87. *)
  Definition bound_len:N := 65.
  Definition t := ((bv bound_len) * (bv bound_len))%type.
  Definition of_Zs (bounds : Z * Z) : t :=
    let '(base,limit) := bounds in   
    (Z_to_bv bound_len base, Z_to_bv bound_len limit). 
  Definition to_Zs (bounds : t) : Z * Z :=
    let (base,top) := bounds in   
    (bv_to_Z_unsigned base, bv_to_Z_unsigned top).

  Definition address_is_in_interval (bounds:t) (value:ValueBV.t) : bool :=
    let '(base,limit) := bounds in 
    let value : (bv bound_len) := bv_to_bv value in 
    (base <=? value) && (value <? limit).

  (* Vadim: is this what we want? *)
  Definition ltb (a b:t) := 
    let '(base_a, limit_a) := a in
    let '(base_b, limit_b) := b in
    ((base_a <? base_b) && (limit_a <=? limit_b))
    || ((base_a <=? base_b) && (limit_a <? limit_b)).

End BoundsBV. 


Module Cap <: Capability (ValueBV) (ObjTypeBV) (SealType) (BoundsBV) (PermissionsBV).
  Definition len:N := 129.
  Definition t := bv len.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
     
  Definition cap_SEAL_TYPE_UNSEALED : ObjTypeBV.t := ObjTypeBV.of_Z 0.
  Definition cap_SEAL_TYPE_RB : ObjTypeBV.t := ObjTypeBV.of_Z 1. 
  Definition cap_SEAL_TYPE_LPB : ObjTypeBV.t := ObjTypeBV.of_Z 2. 
  Definition cap_SEAL_TYPE_LB : ObjTypeBV.t := ObjTypeBV.of_Z 3.

  Definition sizeof_vaddr := 8%nat. (* in bytes *)
  (* Definition vaddr_bits := sizeof_vaddr * 8. *)
  Definition min_vaddr := Z_to_bv (N.of_nat (sizeof_vaddr*8)) 0.  
  Definition max_vaddr := Z_to_bv (N.of_nat (sizeof_vaddr*8)) (bv_modulus (N.of_nat (sizeof_vaddr*8))).
  
  Definition cap_c0 (u:unit) : t := mword_to_bv (CapNull u).

  Definition cap_cU (u:unit) : t := mword_to_bv (concat_vec (Ones 19) (Zeros 110)).

  Definition bound_null (u:unit) : bv 65 := Z_to_bv 65 0.

  Definition cap_flags_len := 8 % nat.
  Definition Flags := { l : list bool | length l = cap_flags_len }.
  
  Definition cap_get_value (cap:t) : ValueBV.t := 
    mword_to_bv (CapGetValue (bv_to_mword cap)).
  
  Definition cap_get_obj_type (cap:t) : ObjTypeBV.t := 
    mword_to_bv (CapGetObjectType (bv_to_mword cap)).

  Definition cap_get_bounds_ (cap:t) : BoundsBV.t * bool :=
    let '(base_mw, limit_mw, isExponentValid) := CapGetBounds (bv_to_mword cap) in
    let base_bv := mword_to_bv base_mw in
    let limit_bv := mword_to_bv limit_mw in 
    ((base_bv, limit_bv), isExponentValid).
  
  Definition cap_get_bounds (cap:t) : BoundsBV.t :=
      let '(base_mw, limit_mw, isExponentValid) := 
        cap_get_bounds_ cap in
      (base_mw, limit_mw).
  
  Definition cap_get_offset (cap:t) : Z :=
    (mword_to_bv (CapGetOffset (bv_to_mword cap))).(bv_unsigned).
        
  Definition cap_get_seal (cap:t) : SealType.t := 
    let ot:ObjTypeBV.t := cap_get_obj_type cap in
    if (ot =? cap_SEAL_TYPE_UNSEALED)%stdpp then SealType.Cap_Unsealed else
    if (ot =? cap_SEAL_TYPE_RB)%stdpp then SealType.Cap_SEntry else
    if (ot =? cap_SEAL_TYPE_LPB)%stdpp then SealType.Cap_Indirect_SEntry else 
    if (ot =? cap_SEAL_TYPE_LB)%stdpp then SealType.Cap_Indirect_SEntry else (* confirm duplication *)
    SealType.Cap_Sealed ot.
    
  (* The flags are the top byte of the value. *)
  Program Definition cap_get_flags (cap:t) : Flags := 
    let m : (mword _) := subrange_vec_dec (bv_to_mword cap) CAP_VALUE_HI_BIT CAP_FLAGS_LO_BIT in
    let l : (list bool) := (mword_to_list_bool m) in
    exist _ l _.
  Next Obligation. reflexivity. Defined.  

  (* Definition cap_get_flags (cap:t) : list bool := 
  let m : (mword _) := subrange_vec_dec (bv_to_mword cap) CAP_VALUE_HI_BIT CAP_FLAGS_LO_BIT in
  let l : (list bool) := (mword_to_list_bool m) in
  l. *)

  Definition cap_get_perms (cap:t) : PermissionsBV.t := 
    mword_to_bv (CapGetPermissions (bv_to_mword cap)).

  Definition cap_is_sealed (cap:t) : bool :=
    CapIsSealed (bv_to_mword cap).
  
  Definition cap_invalidate (cap:t) : t := mword_to_bv (CapWithTagClear (bv_to_mword cap)).

  Definition cap_set_value (cap:t) (value:ValueBV.t) : t :=
    let new_cap := mword_to_bv (CapSetValue (bv_to_mword cap) (bv_to_mword value)) in 
    if (cap_is_sealed cap) then (cap_invalidate new_cap) else new_cap.
  
  Definition cap_set_flags (cap:t) (f: Flags) : t :=
    let new_cap :=
      let flags_m : (mword (Z.of_nat cap_flags_len)) := of_bools (proj1_sig f) in
      let flags' : (mword 64) := concat_vec flags_m (Zeros (64 - (Z.of_nat cap_flags_len))) in 
        mword_to_bv (CapSetFlags (bv_to_mword cap) flags')       in 
    if (cap_is_sealed cap) then (cap_invalidate new_cap) else new_cap.
  
  (* Definition cap_set_flags (cap:t) (f: list bool) : t :=
    let new_cap :=
      let flags_m : (mword (Z.of_nat cap_flags_len)) := of_bools f in
      let flags' : (mword 64) := concat_vec flags_m (Zeros (64 - (Z.of_nat cap_flags_len))) in 
        mword_to_bv (CapSetFlags (bv_to_mword cap) flags')       in 
    if (cap_is_sealed cap) then (cap_invalidate new_cap) else new_cap. *)
  
  Definition cap_set_objtype (cap:t) (ot:ObjTypeBV.t) : t :=
    mword_to_bv (CapSetObjectType (bv_to_mword cap) (zero_extend (bv_to_mword ot) 64)).

  (* [perms] must contain [1] for permissions to be cleared and [0] for those to be kept *)
  Definition cap_narrow_perms (cap:t) (perms:PermissionsBV.t) : t :=
    let perms_mw : (mword (Z.of_N PermissionsBV.len)) := bv_to_mword perms in 
    let mask : (mword 64) := 
      zero_extend perms_mw 64 in
    let new_cap := mword_to_bv (CapClearPerms (bv_to_mword cap) mask) in 
    if (cap_is_sealed cap) then (cap_invalidate new_cap) else new_cap.

  Definition cap_clear_global_perm (cap:t) : t := 
    cap_narrow_perms cap (list_bool_to_bv (PermissionsBV.make_permissions [PermissionsBV.Global_perm])).

  Definition cap_set_bounds (cap : t) (bounds : BoundsBV.t) (exact : bool) : t :=
    (* CapSetBounds sets the lower bound to the value of the input cap,
       so we first have to set the value of cap to bounds.base. *)
    let '(base,limit) := bounds in
    let base_as_val : ValueBV.t := bv_to_bv base in  
    let new_cap := cap_set_value cap base_as_val in 
    let req_len : (mword (Z.of_N BoundsBV.bound_len)) := 
      mword_of_int (Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base)) in 
    let new_cap := 
      mword_to_bv (CapSetBounds (bv_to_mword new_cap) req_len exact) in 
    if (cap_is_sealed cap) then (cap_invalidate new_cap) else new_cap.

  Definition cap_narrow_bounds (cap : t) (bounds : BoundsBV.t) : t :=
    cap_set_bounds cap bounds false.

  Definition cap_narrow_bounds_exact (cap : t) (bounds : BoundsBV.t) : t :=
    cap_set_bounds cap bounds true.

  Definition cap_is_valid (cap:t) : bool := Bool.eqb (CapIsTagClear (bv_to_mword cap)) false.

  Definition cap_is_invalid (cap:t) : bool := negb (cap_is_valid cap).
    
  Definition cap_is_unsealed (cap:t) : bool := negb (cap_is_sealed cap).
  
  Definition cap_is_in_bounds (cap:t) : bool := CapIsInBounds (bv_to_mword cap).

  Definition cap_is_not_in_bounds (cap:t) : bool := negb (cap_is_in_bounds cap).  
  
  Definition cap_is_exponent_out_of_range (cap:t) : bool :=
    CapIsExponentOutOfRange (bv_to_mword cap).

  Definition cap_has_perm (cap:t) :=
    let perms : (mword 64) := zero_extend (bv_to_mword (cap_get_perms cap)) 64 in 
    fun perm => CapPermsInclude perms perm.

  Definition cap_has_seal_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_SEAL.

  Definition cap_has_unseal_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_UNSEAL.

  Definition cap_has_global_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_GLOBAL.

  Definition cap_seal (c : t) (k : t) : t :=
    let key : ObjTypeBV.t := (cap_get_value k) in 
    let sealed_cap := cap_set_objtype c key in 
    if (cap_is_valid c) && (cap_is_valid k) && 
       (cap_is_unsealed c) && (cap_is_unsealed k) && 
       (cap_has_seal_perm k) && (cap_is_in_bounds k) &&
       (Z.to_N (bv_to_Z_unsigned key) <=? ObjTypeBV.CAP_MAX_OBJECT_TYPE)%N then 
       sealed_cap
    else
       cap_invalidate sealed_cap.

  Definition cap_unseal (sealed_cap:t) (unsealing_cap:t) : t :=
    let value := cap_get_value unsealing_cap in 
    let key := cap_get_obj_type sealed_cap in 
    let unsealed_sealed_cap := mword_to_bv (CapUnseal (bv_to_mword sealed_cap)) in 
    let unsealed_sealed_cap := 
      if (negb (cap_has_global_perm unsealing_cap)) then
        cap_clear_global_perm unsealed_sealed_cap
      else unsealed_sealed_cap in 
    if (cap_is_valid sealed_cap && cap_is_valid unsealing_cap 
        && cap_is_sealed sealed_cap && cap_is_unsealed unsealing_cap
        && cap_has_unseal_perm unsealing_cap
        && cap_is_in_bounds unsealing_cap && (key =? value) ) then 
      unsealed_sealed_cap
    else 
      cap_invalidate unsealed_sealed_cap.

  Definition cap_seal_immediate (cap : t) (seal_ot : ObjTypeBV.t) 
    `{ArithFact ((bv_to_Z_unsigned seal_ot >? 0)%Z && (bv_to_Z_unsigned seal_ot <=? 4)%Z)} : t :=
    let new_cap := cap_set_objtype cap seal_ot in 
    if (cap_is_valid cap && cap_is_unsealed cap) then 
      new_cap
    else
      cap_invalidate new_cap.

  (* For sealing with RB *)
  Definition cap_seal_entry (cap:t) : t := 
    cap_seal_immediate cap SealType.sealed_entry_ot.

  (* For sealing with LB *)
  Definition cap_seal_indirect_entry (cap:t) : t := 
    cap_seal_immediate cap SealType.sealed_indirect_entry_ot.

  (* For sealing with LPB *)  
  Definition cap_seal_indirect_entry_pair (cap:t) : t := 
    cap_seal_immediate cap SealType.sealed_indirect_entry_pair_ot.

  (* Confirm the type of the function is ok *)  
  Definition representable_alignment_mask (len:Z) : Z :=
    mword_to_Z_unsigned (CapGetRepresentableMask (@mword_of_int (Z.of_N ValueBV.len) len)).

  (* Will need to see how this compares with Microsoft's Small Cheri 
  (Technical report coming up -- as of Oct 24 2022) *)
  Definition representable_length (len : Z) : Z :=
    let mask:Z := representable_alignment_mask len in
    let nmask:Z := ValueBV.bitwise_complement mask in
    let result:Z := Z.land (Z.add len nmask) mask in 
      result.

  Definition make_cap (value : ValueBV.t) (otype : ObjTypeBV.t) (bounds : BoundsBV.t) (perms : PermissionsBV.t) : t :=
    let new_cap := cap_cU () in 
    let perms_to_clear := list_bool_to_bv (map negb (bv_to_list_bool perms)) in 
    let new_cap := cap_narrow_perms new_cap perms_to_clear in 
    let new_cap := cap_narrow_bounds new_cap bounds in 
    let new_cap := cap_set_value new_cap value in 
      cap_set_objtype new_cap otype.
    
  (* Should we check that size is not too large? *)
  Definition alloc_cap (a_value : ValueBV.t) (size : ValueBV.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_UNSEALED 
      (BoundsBV.of_Zs (bv_to_Z_unsigned a_value, Z.add (bv_to_Z_unsigned a_value) (bv_to_Z_unsigned size)))
      (PermissionsBV.perm_alloc).
    
  Definition alloc_fun (a_value : ValueBV.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_RB 
      (BoundsBV.of_Zs (bv_to_Z_unsigned a_value, Z.succ (Z.succ (bv_to_Z_unsigned a_value)))) 
      PermissionsBV.perm_alloc_fun.

  Definition value_compare (cap1 cap2 : t) : comparison :=
    if (cap_get_value cap1 =? cap_get_value cap2)%stdpp then Eq
    else if (cap_get_value cap1 <? cap_get_value cap2) then Lt
    else Gt.

  Definition exact_compare (cap1 cap2 : t) : comparison :=
    if (cap1 =? cap2) then Eq 
    else if (cap1 <? cap2) then Lt 
    else Gt.

  Definition cap_vaddr_representable (c : t) (a : ValueBV.t) : bool :=
    CapIsRepresentable (bv_to_mword c) (bv_to_mword a).
  
  Definition cap_bounds_representable_exactly (cap : t) (bounds : BoundsBV.t) : bool :=
    let '(base, limit) := bounds in
    let len := Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base) in
    let base' : (bv ValueBV.len) := 
      Z_to_bv ValueBV.len (bv_to_Z_unsigned base) in 
    let len' := mword_of_int (len:=Z.of_N BoundsBV.bound_len) len in 
    let new_cap : (bv _) := cap_set_value cap base' in
    let new_cap : (mword _) := CapSetBounds (bv_to_mword new_cap) len' true in
    CapIsTagSet new_cap.

  Definition cap_is_null_derived (cap : t) : bool :=
    let a := cap_get_value cap in
    let c0 := cap_c0 () in
    let c' := cap_set_value c0 a in
    cap =? c'.
    
  (* Extracted from https://github.com/vzaliva/cerberus/blob/master/coq/Utils.v *)  
  Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
    (* | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a0; a1; a2; a3; a4; a5; a6; a7] *)
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a7; a6; a5; a4; a3; a2; a1; a0]
    end
  in
  List.fold_left (fun l a => List.app l (ascii_to_bits a)) bytes [].  

  (* Definition bool_bits_of_bytes (bytes : list ascii): list bool :=
    let ascii_to_bits (x:ascii) :=
      match x with
      | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a0; a1; a2; a3; a4; a5; a6; a7]
      end in 
    List.flat_map ascii_to_bits bytes. *)
   
  (* Internal helper function to conver between Sail bytes ([memory_byte])
     and Cerberus bytes ([ascii]). *)
  Definition memory_byte_to_ascii (b:memory_byte) : option ascii :=
    match List.map bool_of_bit b with
    | [a1;a2;a3;a4;a5;a6;a7;a8] => Some (Ascii a8 a7 a6 a5 a4 a3 a2 a1)
    | _ => None
    end.

  (* Extracted from https://github.com/vzaliva/cerberus/blob/master/coq/Utils.v *)
  (* could be generalized as monadic map, or implemente as compistion
   of [map] and [sequence]. *)
  Fixpoint try_map {A B:Type} (f : A -> option B) (l:list A) : option (list B)
  :=
  match l with
  | [] => Some []
  | a :: t =>
      match f a with
      | Some b =>
          match try_map f t with
          | Some bs =>  Some (b :: bs)
          | None => None
          end
      | None => None
      end
  end.

  Definition encode (isexact : bool) (cap : t) : option ((list ascii) * bool) :=
    let tag : bool := cap_is_valid cap in 
    let cap_bits := bits_of (bv_to_mword cap) in 
    let w : (mword _) := vec_of_bits (List.tail cap_bits) in
    match mem_bytes_of_bits w with
    | Some bytes =>
        match try_map memory_byte_to_ascii bytes with
        | Some chars => Some ((*List.rev*) chars, tag)
        | None => None
        end
    | None => None
    end.

  Definition decode (bytes : list ascii) (tag : bool) : option (bv Cap.len) :=
    if Nat.eq_dec (List.length bytes) 16%nat then
      let bytes := List.rev bytes in (* TODO: Delete this? *)
      let bits : (list bool) := tag::(bool_bits_of_bytes bytes) in
      let bitsu := List.map bitU_of_bool bits in
      let w : (mword _) := vec_of_bits bitsu in
      (* Some (mword_to_bv w) *) (* This requires the proof below, but makes tests harder *)
      let z : Z := mword_to_Z_unsigned w in 
      let c : option (bv Cap.len) := Z_to_bv_checked Cap.len z in 
      c
    else
      None.
    (* Next Obligation.      
      intros. assert (P: length bytes = 16%nat).
      - unfold bytes. rewrite rev_length. apply e.
      - assert (Q: length (bool_bits_of_bytes bytes) = 128%nat).
        + assert (X: forall (bs:list ascii), length (bool_bits_of_bytes bs) = (8 * (length bs))%nat).
          { induction bs as [| h tl HInd].
          - reflexivity.
          - simpl bool_bits_of_bytes. rewrite app_length. destruct h.
            simpl length. rewrite HInd. 
            assert (T: (8 + 8 * base.length tl)%nat = (8*1 + 8 * base.length tl)%nat).
            + reflexivity.
            + rewrite T. rewrite <- mult_plus_distr_l. reflexivity. }
          rewrite X. rewrite P. reflexivity.
          + assert (R: length bits = 129%nat). 
            -- unfold bits. rewrite list.cons_length. rewrite Q. reflexivity. 
            -- unfold bitsu. unfold length_list. rewrite map_length. rewrite R. reflexivity.
    Defined. *)  

  Definition eqb (cap1:t) (cap2:t) : bool := (cap1 =? cap2)%stdpp.

  Definition to_string (cap:t) : string :=
    String.hex_string_of_int (bv_to_Z_unsigned cap).

  Definition strfcap (s:string) (_:t) : option string := None.
    
  (* Could also implement a prettier to_string that produces something like
    { valid: yes
      value: 0xF...1
      base: 0xF...
      limit: ...
      seal: RB
      permissions: Load,Store,Execute
      flags: 10010...  
    }   *)  

  Lemma eqb_value_compare: forall a b, eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: a = b).
    { unfold eq in H. rewrite -> Z.eqb_eq in H. apply bv_eq. apply H. }
    rewrite <- P. unfold value_compare. unfold eq. rewrite Z.eqb_refl. reflexivity. Qed.
        
  Lemma eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb. unfold exact_compare. destruct (a =? b).
      + reflexivity.
      + destruct (b >? a). 
        { discriminate. } { discriminate. }
    Qed.
    
End Cap.  


 Module test_cap_getters_and_setters.

  Import Cap.

  (* Compute decode (match test_cap_0_enc with Some (l,b) => l | None => [] end) true.
  Compute decode (match test_cap_01_enc with Some (l,b) => l | None => [] end) true. *)

  Definition test_cap_7_encoded:(list ascii) := 
  ["021"%char; "255"%char; "255"%char; "255"%char; "000"%char;
  "000"%char; "000"%char; "000"%char; "021"%char; "255"%char;
  "028"%char; "127"%char; "000"%char; "000"%char; "000"%char;
  "L"%char].
Definition test_cap_7_decoded:(option t) :=
    decode test_cap_7_encoded true.
(* Compute test_cap_7_decoded. *)


  Definition c1:Cap.t := mword_to_bv (concat_vec (Ones 19) (Zeros 110)). (* A valid universal-permission cap = 1^{19}0^{110} *)
  Definition c2:Cap.t := mword_to_bv (concat_vec (Ones 3) (Zeros 126)). (* A valid cap with Load and Store perms *)
  Definition c3:Cap.t := Cap.of_Z 0x1fc000000333711170000000012342222. (* The default cap on https://www.morello-project.org/capinfo *)
  Definition c4:Cap.t := Cap.of_Z 0x1fc000000399700070000000012342222. (* The bounds in this cap subsume those of c3 *)
  Definition c5:Cap.t := Cap.of_Z 0x1fb000000377700070011111111113333. (* Cap breakdown: https://www.morello-project.org/capinfo?c=0x1%3Afb00000037770007%3A0011111111113333 *)
  Definition c6:Cap.t := Cap.of_Z 0x1fb0000007a4700000000000000003333. (* Cap breakdown: https://www.morello-project.org/capinfo?c=0x1%3Afb0000007a470000%3A0000000000003333 *)
  Definition c7:Cap.t := Cap.of_Z 0x14C0000007F1CFF1500000000FFFFFF15.
  Definition c8:Cap.t := Cap.of_Z 0x1900000007f1cff1500000000ffffff15.
                                  
  
  Program Definition flags1:Cap.Flags := exist _ [false; false; false; false; false; false; false; false] _. 
    Next Obligation. reflexivity. Defined.
  Program Definition flags2:Cap.Flags := exist _ [false; true; false; true; false; true; false; true] _. 
    Next Obligation. reflexivity. Defined.
  (* Definition flags1:list bool := [false; false; false; false; false; false; false; false]. 
  Definition flags2:list bool := [false; true; false; true; false; true; false; true].  *)
    
  Definition perm_Load : list bool := PermissionsBV.make_permissions [PermissionsBV.Load_perm].
  Definition perm_Load_Store : list bool := PermissionsBV.make_permissions [PermissionsBV.Load_perm; PermissionsBV.Store_perm].
  Definition perm_Load_Execute : list bool := PermissionsBV.make_permissions [PermissionsBV.Load_perm; PermissionsBV.Execute_perm].
  
  Example is_valid_test_1 :
    cap_is_valid c1 = true.
    Proof. reflexivity. Qed.

  Example is_valid_test_2 :
    cap_is_valid (cap_c0 ()) = false.
    Proof. reflexivity. Qed.

  Example is_valid_test_3 :
    cap_is_valid c5 = true.
    Proof. reflexivity. Qed.

  Example is_valid_test_4 :
    cap_is_valid c2 = true.
    Proof. reflexivity. Qed.

  Example value_test_1 : 
    let value:ValueBV.t := ValueBV.of_Z 50 in
    value = cap_get_value (cap_set_value c1 value).
    Proof. reflexivity. Qed. 

  Example flags_test_1 : flags1 = cap_get_flags c1.
    Proof. reflexivity. Qed.

  Example flags_test_2 : flags2 = cap_get_flags (cap_set_flags c1 flags2).
    Proof. reflexivity. Qed. 
  
  Import PermissionsBV.
  
  Example permissions_test_1 : 
    PermissionsBV.perm_Universal = cap_get_perms c1.
    Proof. reflexivity. Qed.

  Example permissions_test_2 : 
    let mask : PermissionsBV.t := list_bool_to_bv (map negb perm_Load_Store) in
    list_bool_to_bv perm_Load_Store = cap_get_perms (cap_narrow_perms c1 mask).
    Proof. reflexivity. Qed.

  Example permissions_test_3 : 
    let mask : PermissionsBV.t := list_bool_to_bv (map negb perm_Load_Store) in
    let cap := (cap_narrow_perms c1 mask) in 
    let mask : PermissionsBV.t := list_bool_to_bv (map negb perm_Load_Execute) in
    list_bool_to_bv perm_Load = cap_get_perms (cap_narrow_perms cap mask).
    Proof. vm_compute. reflexivity. Qed.

  Example permissions_test_4 : 
    let mask : PermissionsBV.t := list_bool_to_bv (map negb (make_permissions [Load_perm; Execute_perm])) in  
    let capA := (cap_narrow_perms c1 mask) in     
    let perms : PermissionsBV.t := PermissionsBV.perm_Universal in 
    let perms := perm_clear_store_cap perms in 
    let perms := perm_clear_store perms in 
    let perms := perm_clear_global perms in 
    let perms := perm_clear_executive perms in 
    let perms := perm_clear_seal perms in 
    let perms := perm_clear_load_cap perms in 
    let perms := perm_clear_store_local_cap perms in 
    let perms := perm_clear_system_access perms in 
    let perms := perm_clear_unseal perms in 
    let perms := perm_clear_branch_sealed_pair perms in 
    let perms := perm_clear_mutable_load perms in 
    let perms := perm_clear_compartment_ID perms in 
    let perms := perm_clear_user4 perms in 
    let perms := perm_clear_user3 perms in 
    let perms := perm_clear_user2 perms in 
    let perms := perm_clear_user1 perms in 
    let perms := PermissionsBV.of_list (map negb (PermissionsBV.to_list perms)) in
    let capB := (cap_narrow_perms c1 (match perms with Some p => p | None => PermissionsBV.perm_Universal end)) in
    capA = capB.
    Proof. vm_compute. reflexivity. Qed.

  Example get_and_user_perms_test_1 : 
    let user_perms_A : (list bool) := get_user_perms (cap_get_perms (cap_cU ())) in 
    let user_perms_A := [ nth 0 user_perms_A false; negb (nth 1 user_perms_A false);
                        nth 2 user_perms_A false; negb (nth 3 user_perms_A false) ] in 
    let user_perms_B : PermissionsBV.t := 
      perm_and_user_perms (cap_get_perms (cap_cU ())) user_perms_A in
      user_perms_A = [true; false; true; false] /\
      get_user_perms user_perms_B = user_perms_A.
    Proof. vm_compute. split. reflexivity. reflexivity. Qed. 
 
  Example eqb_and_narrow_perm_test_1 :
    let mask : PermissionsBV.t := list_bool_to_bv (map negb perm_Load_Store) in
    (c2 = (cap_narrow_perms c1 mask))%stdpp.
    Proof. vm_compute. reflexivity. Qed.

  Example bounds_representable_exactly_test_1 :
    let bounds : BoundsBV.t := 
      (Z_to_bv BoundsBV.bound_len 305402128, Z_to_bv BoundsBV.bound_len 305427248) in (* the bounds of c3, which we know is representable *) 
    cap_bounds_representable_exactly c4 bounds = true.
    Proof. reflexivity. Qed. 
      
  Example bounds_representable_exactly_test_2 :
    let bounds : BoundsBV.t := 
      (Z_to_bv BoundsBV.bound_len 305402128, Z_to_bv BoundsBV.bound_len 306427248) in (* now we changed the common part of the bounds *) 
    cap_bounds_representable_exactly c4 bounds = false.
    Proof. reflexivity. Qed. 
  
  Example narrow_exact_and_get_bounds_test_1 : 
    (* The bounds of capability c5 are         (0x0011111111110000, 0x00011111111117770). *)
    let '(new_base,new_limit) := BoundsBV.of_Zs  (0x0011111111113330, 0x00011111111117440) in 
    (* We can see new_bounds can be represented exactly from cap5: https://www.morello-project.org/capinfo?c=0x1%3Afb00000034473337%3A1011111111113333 *)
    let new_cap := cap_narrow_bounds_exact c5 (new_base,new_limit) in 
    let result := cap_get_bounds new_cap in 
    (* isExpValid = true /\ (base_set =? new_base) = true /\  *)
    (* (limit_set =? new_limit) = true *) 
    (cap_is_valid c5) = true /\ (cap_is_valid new_cap) = true
    /\ cap_get_bounds_ new_cap = (new_base,new_limit,true).
    Proof. vm_compute. split. reflexivity. split. reflexivity. (* split. reflexivity. 
      split. reflexivity. *) reflexivity. Qed. 
  
  Example seal_and_unseal_test_1 :
    (* c6 has Seal and Unseal permissions and its value is <= the largest objtype. *) 
    let sealed_cap := cap_seal c3 c6 in
    let unsealed_sealed_cap := cap_unseal sealed_cap c6 in 
    (cap_is_valid sealed_cap) = true /\ (cap_is_sealed sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap) = (cap_get_value c6) 
    /\ (cap_is_valid unsealed_sealed_cap) = true /\ (cap_is_unsealed unsealed_sealed_cap) = true.
    Proof. vm_compute. repeat ( split; try reflexivity ). Qed.

  Example seal_entry_test_1 : 
    let sealed_cap := cap_seal_entry c4 in 
    let sealed_sealed_cap := cap_seal_entry sealed_cap in 
    let sealed_invalid_cap := cap_seal_entry (cap_invalidate c4) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_entry_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed. 

  Example seal_indirect_entry_test_1 : 
    let sealed_cap := cap_seal_indirect_entry c3 in 
    let sealed_sealed_cap := cap_seal_indirect_entry sealed_cap in 
    let sealed_invalid_cap := cap_seal_indirect_entry (cap_invalidate c3) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_indirect_entry_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed.
      
  Example seal_indirect_entry_pair_test_1 : 
    let sealed_cap := cap_seal_indirect_entry_pair c5 in 
    let sealed_sealed_cap := cap_seal_indirect_entry_pair sealed_cap in 
    let sealed_invalid_cap := cap_seal_indirect_entry_pair (cap_invalidate c5) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_indirect_entry_pair_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed.
        
  Example alloc_cap_test_1 : 
    let value := ValueBV.of_Z 1024 in 
    let new_cap := alloc_cap value (ValueBV.of_Z 2048) in 
    (cap_is_valid new_cap) /\ (cap_get_value new_cap) = value 
    /\ (cap_is_in_bounds new_cap) /\ (cap_is_sealed new_cap) = false 
    /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = PermissionsBV.perm_alloc
    /\ (cap_get_bounds_ new_cap) = (BoundsBV.of_Zs (1024,3072), true).
    Proof. vm_compute. repeat (split; try reflexivity). Qed. 
  
  Example alloc_cap_test_2 : 
    let value := ValueBV.of_Z 0xffffffffffffffff in (* 16 f's = the largest Value possible *)
    let new_cap := alloc_cap value (ValueBV.of_Z 1) in 
    (cap_is_valid new_cap) = true /\ (cap_get_value new_cap) = value 
    /\ (cap_is_in_bounds new_cap) /\ (cap_is_sealed new_cap) = false 
    /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = PermissionsBV.perm_alloc
    /\ (cap_get_bounds_ new_cap) = (BoundsBV.of_Zs (0xffffffffffffffff,0x10000000000000000), true).
    Proof. vm_compute. repeat (split; try reflexivity). Qed. 

  Example alloc_cap_test_3 : 
    let value := ValueBV.of_Z 0x10000000000000000 in (* 1 past the largest Value possible; it gets passed as just 0 *)
    let new_cap := alloc_cap value (ValueBV.of_Z 1) in 
    (cap_is_valid new_cap) = true 
    /\ (cap_is_in_bounds new_cap) = true (* it's in bounds bc these are (0,1) *)
    /\ (cap_is_sealed new_cap) = false /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = PermissionsBV.perm_alloc  
    /\ (cap_get_bounds_ new_cap) <> (BoundsBV.of_Zs (0x10000000000000000,0x10000000000000001), true).
    Proof. vm_compute. repeat (split; try reflexivity). intros H. discriminate H. Qed.

  Example alloc_cap_test_4 : 
    let value := ValueBV.of_Z 0xffffffffffffff in (* 14 f's *)
    let new_cap := alloc_cap value (ValueBV.of_Z 0xfff) in (* this sends the limit above the max limit allowed *)
    (cap_is_invalid new_cap) /\ (cap_is_not_in_bounds new_cap)
    /\ (cap_is_sealed new_cap) = false /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = PermissionsBV.perm_alloc  
    /\ (cap_get_bounds_ new_cap) <> (BoundsBV.of_Zs (0xffffffffffffff,0xfffffffffffffffff), true).
    Proof. vm_compute. repeat (split; try reflexivity). intro H. discriminate H. Qed.   
          
  Example alloc_fun_test_1 : 
    let value := ValueBV.of_Z 1024 in 
    let new_cap := alloc_fun value in 
    (cap_is_valid new_cap) = true /\ (cap_get_value new_cap) = value 
      /\ (cap_is_sealed new_cap) = true /\ (cap_get_seal new_cap) = SealType.Cap_SEntry 
      /\ (cap_get_perms new_cap) = PermissionsBV.perm_alloc_fun
      /\ (cap_get_bounds_ new_cap) = (BoundsBV.of_Zs (1024,1026), true).
    Proof. repeat (split; try reflexivity). Qed. 

  Example cap_is_null_derived_test_1 : 
    let new_cap := cap_c0 () in 
    let new_cap := cap_set_value new_cap (ValueBV.of_Z 512) in 
    (cap_is_null_derived new_cap) = true.
    Proof. vm_compute. reflexivity. Qed.
      
  Example cap_is_null_derived_test_2 : 
    let new_cap := cap_cU () in 
    let new_cap := cap_set_value new_cap (ValueBV.of_Z 512) in 
    (cap_is_null_derived new_cap) = false.
    Proof. vm_compute. reflexivity. Qed.

  Example encode_and_decode_test_1 :     
    let tester := fun cap:Cap.t => 
      let encoded_cap : option ((list ascii) * bool) := encode true cap in 
      let decoded_cap : option Cap.t :=
        match encoded_cap with 
          Some (l,tag) => (decode l tag) | None => None
        end in 
      let c_ : Cap.t := 
        match decoded_cap with 
          Some c => c | None => cap_c0 () 
        end in 
        (c_ =? cap) = true in
      tester c1 /\ tester c2 /\ tester c3 /\ tester c4 /\ tester c5 /\ tester c6 
      /\ tester c7 /\ tester c8.
    Proof. vm_compute. repeat (split; try reflexivity). Qed.
 
End test_cap_getters_and_setters. 

Module Permissions <: Permission. 
  Definition t := Z. 

  Definition user_perms_len := PermissionsBV.user_perms_len.

  Definition has_global_perm (perms:t) : bool := 
    PermissionsBV.has_global_perm (PermissionsBV.of_Z perms).
   
  Definition has_execute_perm (perms:t) : bool := 
    PermissionsBV.has_execute_perm (PermissionsBV.of_Z perms).
  Definition has_ccall_perm (perms:t) : bool := 
    PermissionsBV.has_ccall_perm (PermissionsBV.of_Z perms).
  Definition has_load_perm (perms:t) : bool := 
    PermissionsBV.has_load_perm (PermissionsBV.of_Z perms).
  Definition has_load_cap_perm (perms:t) : bool := 
    PermissionsBV.has_load_cap_perm (PermissionsBV.of_Z perms).
  Definition has_seal_perm (perms:t) : bool := 
    PermissionsBV.has_seal_perm (PermissionsBV.of_Z perms).
  Definition has_store_perm (perms:t) : bool := 
    PermissionsBV.has_store_perm (PermissionsBV.of_Z perms).
  Definition has_store_cap_perm (perms:t) : bool := 
    PermissionsBV.has_store_cap_perm (PermissionsBV.of_Z perms).
  Definition has_store_local_cap_perm (perms:t) : bool := 
    PermissionsBV.has_store_local_cap_perm (PermissionsBV.of_Z perms).
  Definition has_system_access_perm (perms:t) : bool := 
    PermissionsBV.has_system_access_perm (PermissionsBV.of_Z perms).
  Definition has_unseal_perm (perms:t) : bool := 
    PermissionsBV.has_unseal_perm (PermissionsBV.of_Z perms).
  
  Definition get_user_perms (perms:t) : list bool :=
    PermissionsBV.get_user_perms (PermissionsBV.of_Z perms).
 

  Definition perm_clear_global (perms:t) : t := 
    bv_to_Z_unsigned (PermissionsBV.perm_clear_global (PermissionsBV.of_Z perms)).
  
  Definition perm_clear_execute (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_execute (PermissionsBV.of_Z perms)).
  Definition perm_clear_ccall (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_ccall (PermissionsBV.of_Z perms)).
  Definition perm_clear_load (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_load (PermissionsBV.of_Z perms)).
  Definition perm_clear_load_cap (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_load_cap (PermissionsBV.of_Z perms)).
  Definition perm_clear_seal (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_seal (PermissionsBV.of_Z perms)).
  Definition perm_clear_store (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_store (PermissionsBV.of_Z perms)).
  Definition perm_clear_store_cap (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_store_cap (PermissionsBV.of_Z perms)).
  Definition perm_clear_store_local_cap (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_store_local_cap (PermissionsBV.of_Z perms)).
  Definition perm_clear_system_access (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_system_access (PermissionsBV.of_Z perms)).
  Definition perm_clear_unseal (perms:t) : t := bv_to_Z_unsigned (PermissionsBV.perm_clear_unseal (PermissionsBV.of_Z perms)).
  
  (** perform bitwise AND of user permissions *)
  Definition perm_and_user_perms (perms:t) (l:list bool) : t := 
    bv_to_Z_unsigned (PermissionsBV.perm_and_user_perms (PermissionsBV.of_Z perms) l).
 
  (** null permission *)
  Definition perm_p0: t := bv_to_Z_unsigned (PermissionsBV.perm_p0).

  (** permissions for newly allocated region *)
  Definition perm_alloc: t := bv_to_Z_unsigned (PermissionsBV.perm_alloc).

  (** permissions for newly allocated function *)
  Definition perm_alloc_fun: t := bv_to_Z_unsigned (PermissionsBV.perm_alloc_fun).

  (* --- Utility methods --- *)

  Definition to_string (perms:t) : string := PermissionsBV.to_string (PermissionsBV.of_Z perms).
  Definition to_string_hex (perms:t) : string := PermissionsBV.to_string_hex (PermissionsBV.of_Z perms).

  (* raw permissoins in numeric format *)
  Definition to_raw (perms:t) : Z := perms.

  (* Initialize from list of boolean. The size and
     contents of the list is implementation-specific.
     Returns None in case of error *)
  Definition of_list (l:list bool) : option t := 
    match PermissionsBV.of_list l with 
      Some c => Some (bv_to_Z_unsigned c) | None => None
    end.

  (* inverse of [of_list] *)
  Definition to_list (perms:t) : list bool := PermissionsBV.to_list (PermissionsBV.of_Z perms).
End Permissions.

Module Value <: VADDR.
  Definition t := Z.

  Definition bitwise_complement (a:Z) : Z := ValueBV.bitwise_complement a.
    
  Definition eqb (v1:t) (v2:t) : bool := ValueBV.eqb (ValueBV.of_Z v1) (ValueBV.of_Z v2).
  Definition ltb (v1:t) (v2:t) : bool := ValueBV.ltb (ValueBV.of_Z v1) (ValueBV.of_Z v2).
  Definition leb (v1:t) (v2:t) : bool := ValueBV.leb (ValueBV.of_Z v1) (ValueBV.of_Z v2).
  
  Definition ltb_irref: forall a:t, ltb a a = false.
  Proof. intros. unfold ltb. unfold ValueBV.ltb. unfold lt. rewrite Z.ltb_irrefl. reflexivity. Qed. 

  Definition of_Z (z:Z) := z.
  Definition to_Z (v:t) := v.
  
End Value.


Module ObjType <: OTYPE.
  Definition t := Z.  
End ObjType.


Module Bounds <: VADDR_INTERVAL(Value).
  Definition t := (Z * Z)%type.
  
  Definition address_is_in_interval (bounds:t) (value:Value.t) : bool :=
    BoundsBV.address_is_in_interval (BoundsBV.of_Zs bounds) (ValueBV.of_Z value). 

  (* Vadim: is this what we want? *)
  Definition ltb (a b:t) := BoundsBV.ltb (BoundsBV.of_Zs a) (BoundsBV.of_Zs b).

End Bounds. 

Module MorelloCapability <: Capability (Value) (ObjType) (SealType) (Bounds) (Permissions).
  Definition t := Cap.t.
  
  (* Definition vaddr_bits := sizeof_vaddr * 8. *)
  Definition sizeof_vaddr := Cap.sizeof_vaddr. (* in bytes *)
  Definition min_vaddr := ValueBV.to_Z Cap.min_vaddr.  
  Definition max_vaddr := ValueBV.to_Z Cap.max_vaddr.

  Definition cap_c0 := Cap.cap_c0.
  
  Definition cap_flags_len := Cap.cap_flags_len.
  Definition Flags := Cap.Flags.

  Definition cap_get_value (cap:t) : Value.t := 
    ValueBV.to_Z (Cap.cap_get_value cap). 
  
  Definition cap_get_obj_type (cap:t) : ObjType.t := 
    ObjTypeBV.to_Z (Cap.cap_get_obj_type cap).

  (* Removed flag here *)
  Definition cap_get_bounds (cap:t) : Bounds.t :=
    BoundsBV.to_Zs (Cap.cap_get_bounds cap).

  Definition cap_get_offset (cap:t) : Z := Cap.cap_get_offset cap.
      
  Definition cap_get_seal (cap:t) : SealType.t := Cap.cap_get_seal cap. 
  
  (* The flags are the top byte of the value. *)
  Definition cap_get_flags (cap:t) : Flags (* list bool *) := 
    Cap.cap_get_flags cap. 

  Definition cap_get_perms (cap:t) : Permissions.t :=
    PermissionsBV.to_Z (Cap.cap_get_perms cap).
    
  Definition cap_invalidate (cap:t) : t := Cap.cap_invalidate cap.

  Definition cap_set_value (cap:t) (value:Value.t) : t :=
    Cap.cap_set_value cap (ValueBV.of_Z value).
    
  Definition cap_set_flags := Cap.cap_set_flags.
  
  Definition cap_set_objtype (cap:t) (ot:ObjType.t) : t :=
    Cap.cap_set_objtype cap (ObjTypeBV.of_Z ot).
    
  Definition cap_is_sealed := Cap.cap_is_sealed.

  (* [perms] must contain [1] for permissions to be cleared and [0] for those to be kept *)
  Definition cap_narrow_perms (cap:t) (perms:Permissions.t) : t :=
    Cap.cap_narrow_perms cap (PermissionsBV.of_Z perms).
    
  Definition cap_narrow_bounds (cap : t) (bounds : Bounds.t) : t :=
    Cap.cap_narrow_bounds cap (BoundsBV.of_Zs bounds).

  Definition cap_narrow_bounds_exact (cap : t) (bounds : Bounds.t) : t :=
    Cap.cap_narrow_bounds_exact cap (BoundsBV.of_Zs bounds).

  Definition cap_is_valid := Cap.cap_is_valid.

  Definition cap_seal := Cap.cap_seal.
  
  Definition cap_unseal := Cap.cap_unseal.

  (* For sealing with RB *)
  Definition cap_seal_entry := Cap.cap_seal_entry.
  
  (* For sealing with LB *)
  Definition cap_seal_indirect_entry := Cap.cap_seal_indirect_entry.

  (* For sealing with LPB *)  
  Definition cap_seal_indirect_entry_pair := Cap.cap_seal_indirect_entry_pair.
    
  (* Confirm the type of the function is ok *)  
  Definition representable_alignment_mask := Cap.representable_alignment_mask.

  (* Will need to see how this compares with Microsoft's Small Cheri 
  (Technical report coming up -- as of Oct 24 2022) *)
  Definition representable_length := Cap.representable_length.
    
  (* Should we check that size is not too large? *)
  Definition alloc_cap (a_value : Value.t) (size : Value.t) : t :=
    Cap.alloc_cap (ValueBV.of_Z a_value) (ValueBV.of_Z size).
  
  Definition alloc_fun (a_value : Value.t) : t :=
    Cap.alloc_fun (ValueBV.of_Z a_value).

  Definition value_compare := Cap.value_compare.

  Definition exact_compare := Cap.exact_compare.

  Definition cap_vaddr_representable (c : t) (a : Value.t) : bool :=
    Cap.cap_vaddr_representable c (ValueBV.of_Z a).
  
  Definition cap_bounds_representable_exactly (cap : t) (bounds : Bounds.t) : bool :=
    Cap.cap_bounds_representable_exactly cap (BoundsBV.of_Zs bounds).

  Definition cap_is_null_derived := Cap.cap_is_null_derived.
  
  Definition encode := Cap.encode.

  Definition decode := Cap.decode.

  Definition eqb := Cap.eqb.

  Definition to_string := Cap.to_string.

  Definition strfcap (s:string) (_:t) : option string := None.

  (* Could also implement a prettier to_string that produces something like
    { valid: yes
      value: 0xF...1
      base: 0xF...
      limit: ...
      seal: RB
      permissions: Load,Store,Execute
      flags: 10010...  
    }   *)  

  Lemma eqb_value_compare: forall (a b:t), eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: a = b).
    { unfold Cap.eqb in H. unfold eq in H. rewrite -> Z.eqb_eq in H. apply bv_eq. apply H. }
    rewrite <- P. unfold value_compare. unfold Cap.value_compare. unfold eq. rewrite Z.eqb_refl. reflexivity. Qed.
        
  Lemma eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold Cap.eqb. unfold exact_compare. unfold Cap.exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb.  unfold Cap.eqb. unfold exact_compare. unfold Cap.exact_compare. destruct (a =? b).
      + reflexivity.
      + destruct (b >? a). 
        { discriminate. } { discriminate. }
    Qed.

End MorelloCapability.
