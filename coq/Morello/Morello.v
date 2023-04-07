Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.HexString.
Require Import Coq.ZArith.Zdigits.

From stdpp.unstable Require Import bitvector. 
Require Import Sail.Values.
Require Import Sail.Operators_mwords.
Require Import CapFns.
Require Import Common.Utils.

Require Import Capabilities.
Require Import Addr.


(* Notations and their definitions*)

(* Notation "x =? y" := (bool_decide (x = y)) (at level 70, no associativity) . *)
Definition eqb {n} (v1:bv n) (v2:bv n) : bool :=
  v1.(bv_unsigned) =? v2.(bv_unsigned).
Definition ltb {n} (v1:bv n) (v2:bv n) : bool :=
  v1.(bv_unsigned) <? v2.(bv_unsigned).
Definition leb {n} (v1:bv n) (v2:bv n) : bool := 
  ltb v1 v2 || eqb v1 v2.
Definition gtb {n} (v1:bv n) (v2:bv n) : bool := 
  leb v2 v1.

Local Notation "x =? y" := (eqb x y) (at level 70, no associativity).
Local Notation "x <? y" := (ltb x y) (at level 70, no associativity).
Local Notation "x <=? y" := (leb x y) (at level 70, no associativity).
Local Notation "x >? y" := (gtb x y) (at level 70, no associativity).

Local Notation "(<@{ A } )" := (@lt A) (only parsing) : stdpp_scope.
Local Notation LtDecision A := (RelDecision (<@{A})).


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

(* Expects less-significant bits in lower indices *)
Definition list_bool_to_mword (l : list bool) : mword (Z.of_nat (List.length l)) := 
  of_bools (List.rev l). (* TODO: bypass rev *)
  
Definition invert_bits {n} (m : mword n) : (mword n) :=
  let l : list bool := mword_to_list_bool m in 
  let l := map negb l in 
  let x : mword (Z.of_nat (base.length l)) := list_bool_to_mword l in
  let x : Z := int_of_mword false x in 
  mword_of_int x.

Definition N_to_mword (m n : N) : mword (Z.of_N m) := 
  mword_of_int (Z.of_N n).
Program Definition list_bool_to_bv (l : list bool) : bv (N.of_nat (List.length l)) := 
  @mword_to_bv (Z.of_nat (List.length l)) (of_bools (List.rev l)).
 Next Obligation. intros. unfold Z.of_nat. destruct (length l). 
 {reflexivity. } {reflexivity. } Defined.  

Module Permissions <: Permission.
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
    HexString.of_Z (bv_to_Z_unsigned perms). 

  Definition to_raw (perms:t) : Z := bv_to_Z_unsigned perms.

  Definition of_list (l : list bool) : option t := 
    if ((List.length l) <? (N.to_nat len))%nat then
      None 
    else
      Some (@mword_to_bv (Z.of_N len) (of_bools (List.rev (List.firstn (N.to_nat len) l)))).
    (* if ((List.length l) =? (N.to_nat len))%nat then
      Some (@mword_to_bv (Z.of_N len) (of_bools (List.rev l))) 
    else None. *)
  
  Definition to_list (perms:t) : list bool := 
    bv_to_list_bool perms.

  Definition eqb (a b:t) : bool := eqb a b.

End Permissions.


Module AddressValue <: PTRADDR.
  Definition len:N := 64.
  Definition t := bv len.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Definition to_Z (v:t) : Z := bv_to_Z_unsigned v.

  Definition bitwise_complement_Z (a:Z) : Z :=
    let bits := Z_to_binary (N.to_nat len) a in
    let bits := Vector.map negb bits in
    binary_value _ bits.

  Definition bitwise_complement (a:t) : t :=
    of_Z (bitwise_complement_Z (to_Z a)).

  Definition eqb (v1:t) (v2:t) : bool := Morello.eqb v1 v2.
  Definition ltb (v1:t) (v2:t) : bool := Morello.ltb v1 v2.
  Definition leb (v1:t) (v2:t) : bool := Morello.leb v1 v2.

  Definition to_string (v:t) : string := HexString.of_Z (bv_to_Z_unsigned v).
  
  Definition ltb_irref: forall a:t, ltb a a = false.
  Proof. intros. unfold ltb. unfold Morello.ltb. rewrite Z.ltb_irrefl. reflexivity. Qed. 
  
End AddressValue.


Module ObjType <: OTYPE.
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

  Definition eqb (a b:t) : bool := eqb a b.

End ObjType.


Module SealType <: CAP_SEAL_T.
  Inductive cap_seal_t :=
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  | Cap_Indirect_SEntry_Pair (* "LPB" in Morello. TODO see why unused *)
  | Cap_Sealed (seal : ObjType.t).
  
  Definition t := cap_seal_t. 

  Definition get_seal_ot (seal:t) : ObjType.t :=
    match seal with 
      Cap_Unsealed => ObjType.of_Z 0
    | Cap_SEntry => ObjType.of_Z 1
    | Cap_Indirect_SEntry => ObjType.of_Z 3
    | Cap_Indirect_SEntry_Pair => ObjType.of_Z 2
    | Cap_Sealed seal => seal
    end.

  Definition sealed_entry_ot := get_seal_ot Cap_SEntry.
  Definition sealed_indirect_entry_ot := get_seal_ot Cap_Indirect_SEntry.
  Definition sealed_indirect_entry_pair_ot := get_seal_ot Cap_Indirect_SEntry_Pair.

  Definition eqb (a b: t) :=
    match a, b with
    | Cap_Unsealed, Cap_Unsealed => true
    | Cap_SEntry, Cap_SEntry => true
    | Cap_Indirect_SEntry, Cap_Indirect_SEntry => true
    | Cap_Sealed a, Cap_Sealed b => ObjType.eqb a b
    | _, _ => false
    end.

End SealType.


Module Flags <: FLAGS.

  Definition length:nat := 8.
  Definition t := { l : list bool | List.length l = length }.
  Definition eqb (f1:t) (f2:t) : bool := List_bool_eqb (proj1_sig f1) (proj1_sig f2).

End Flags.


Module Bounds <: PTRADDR_INTERVAL(AddressValue).

  (* Definition t := bv 87. *)
  Definition bound_len:N := 65.
  Definition t := ((bv bound_len) * (bv bound_len))%type.
  Definition of_Zs (bounds : Z * Z) : t :=
    let '(base,limit) := bounds in   
    (Z_to_bv bound_len base, Z_to_bv bound_len limit). 
  Definition to_Zs (bounds : t) : Z * Z :=
    let (base,top) := bounds in   
    (bv_to_Z_unsigned base, bv_to_Z_unsigned top).

  Definition address_is_in_interval (bounds:t) (value:AddressValue.t) : bool :=
    let '(base,limit) := bounds in 
    let value : (bv bound_len) := bv_to_bv value in 
    (base <=? value) && (value <? limit).

  Definition ltb (a b:t) := 
    let '(base_a, limit_a) := a in
    let '(base_b, limit_b) := b in
    ((base_a <? base_b) && (limit_a <=? limit_b))
    || ((base_a <=? base_b) && (limit_a <? limit_b)).

  Definition to_string (b:t) : string := 
    let (base,top) := b in 
    HexString.of_Z (bv_to_Z_unsigned base) ++ "-" ++ HexString.of_Z (bv_to_Z_unsigned top).

  Definition eqb (a b:t) : bool :=
    let (a0,a1) := a in
    let (b0,b1) := b in
    eqb a0 b0 && eqb a1 b1.

End Bounds. 


Module Capability <: Capability (AddressValue) (Flags) (ObjType) (SealType) (Bounds) (Permissions).
  Definition len:N := 129.
  Definition cap_t := bv len.

  Inductive morello_cap_t :=
  {
    cap : cap_t;
    ghost_state: CapGhostState
  }.
	
	Definition t := morello_cap_t.

  Definition with_ghost_state gs (r : t) := {| cap := r.(cap); ghost_state := gs |}.

  (** ghost state management **)
  Definition get_ghost_state (c:t) := c.(ghost_state).
  Definition set_ghost_state (c:t) gs := with_ghost_state gs c.
  Definition with_cap (c:t) (cap_:cap_t) : t :=
    {| cap := cap_; ghost_state := get_ghost_state c |}.

  Definition cap_t_to_t (c:cap_t) (gs:CapGhostState) : t := 
    {| cap := c; ghost_state := gs |}.

  Definition cap_to_mword (c:t) : (mword (Z.of_N len)) :=
    bv_to_mword c.(cap).    
  
  Definition of_Z (z:Z) : t := cap_t_to_t (Z_to_bv len z) Default_CapGhostState.
     
  Definition cap_SEAL_TYPE_UNSEALED : ObjType.t := ObjType.of_Z 0.
  Definition cap_SEAL_TYPE_RB : ObjType.t := ObjType.of_Z 1. 
  Definition cap_SEAL_TYPE_LPB : ObjType.t := ObjType.of_Z 2. 
  Definition cap_SEAL_TYPE_LB : ObjType.t := ObjType.of_Z 3.

  Definition sizeof_ptraddr := 8%nat. (* in bytes *)
  (* Definition ptraddr_bits := sizeof_ptraddr * 8. *)
  Definition min_ptraddr := Z_to_bv (N.of_nat (sizeof_ptraddr*8)) 0.  
  Definition max_ptraddr := Z_to_bv (N.of_nat (sizeof_ptraddr*8)) (Z.sub (bv_modulus (N.of_nat (sizeof_ptraddr*8))) 1).

  Definition cap_c0 (u:unit) : t := 
    cap_t_to_t (mword_to_bv (CapNull u)) Default_CapGhostState.

  Definition cap_cU (u:unit) : t := 
    cap_t_to_t (mword_to_bv (concat_vec (Ones 19) (Zeros 110))) Default_CapGhostState.

  Definition bound_null (u:unit) : bv 65 := Z_to_bv 65 0.

  Definition cap_get_value (c:t) : AddressValue.t := 
    mword_to_bv (CapGetValue (bv_to_mword c.(cap))).
  
  Definition cap_get_obj_type (c:t) : ObjType.t := 
    mword_to_bv (CapGetObjectType (bv_to_mword c.(cap))).

  Definition cap_get_bounds_ (c:t) : Bounds.t * bool :=
    let '(base_mw, limit_mw, isExponentValid) := CapGetBounds (bv_to_mword c.(cap)) in
    let base_bv := mword_to_bv base_mw in
    let limit_bv := mword_to_bv limit_mw in 
    ((base_bv, limit_bv), isExponentValid).
  
  Definition cap_get_bounds (cap:t) : Bounds.t :=
      let '(base_mw, limit_mw, isExponentValid) := 
        cap_get_bounds_ cap in
      (base_mw, limit_mw).
  
  Definition cap_get_offset (c:t) : Z :=
    (mword_to_bv (CapGetOffset (bv_to_mword c.(cap)))).(bv_unsigned).
        
  Definition cap_get_seal (cap:t) : SealType.t := 
    let ot:ObjType.t := cap_get_obj_type cap in
    if (ot =? cap_SEAL_TYPE_UNSEALED)%stdpp then SealType.Cap_Unsealed else
    if (ot =? cap_SEAL_TYPE_RB)%stdpp then SealType.Cap_SEntry else
    if (ot =? cap_SEAL_TYPE_LPB)%stdpp then SealType.Cap_Indirect_SEntry else 
    if (ot =? cap_SEAL_TYPE_LB)%stdpp then SealType.Cap_Indirect_SEntry else 
    SealType.Cap_Sealed ot.
    
  (* The flags are the top byte of the value. *)
  Program Definition cap_get_flags (c:t) : Flags.t := 
    let m : (mword _) := subrange_vec_dec (bv_to_mword c.(cap)) CAP_VALUE_HI_BIT CAP_FLAGS_LO_BIT in
    let l : (list bool) := (mword_to_list_bool m) in
    exist _ l _.
  Next Obligation. reflexivity. Defined.  

  Definition cap_get_perms (c:t) : Permissions.t := 
    mword_to_bv (CapGetPermissions (bv_to_mword c.(cap))).

  Definition cap_is_sealed (c:t) : bool :=
    CapIsSealed (bv_to_mword c.(cap)).
  
  Definition cap_invalidate (c:t) : t := 
    with_cap c (mword_to_bv (CapWithTagClear (bv_to_mword c.(cap)))).

  Definition cap_set_value (c:t) (value:AddressValue.t) : t :=
    let new_cap := 
      with_cap c (mword_to_bv (CapSetValue (bv_to_mword c.(cap)) (bv_to_mword value))) in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.
  
  Definition cap_set_flags (c:t) (f: Flags.t) : t :=
    let new_cap :=
      let flags_m : (mword (Z.of_nat Flags.length)) := of_bools (List.rev (proj1_sig f)) in
      let flags' : (mword 64) := concat_vec flags_m (Zeros (64 - (Z.of_nat Flags.length))) in 
      with_cap c (mword_to_bv (CapSetFlags (bv_to_mword c.(cap)) flags'))      in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.
  
  Definition cap_set_objtype (c:t) (ot:ObjType.t) : t :=
    with_cap c (mword_to_bv (CapSetObjectType (bv_to_mword c.(cap)) (zero_extend (bv_to_mword ot) 64))).

  (* [perms] must contain [1] for permissions to be kept and [0] for those to be cleared *)
  Definition cap_narrow_perms (c:t) (perms:Permissions.t) : t :=
    let perms_mw : (mword (Z.of_N Permissions.len)) := bv_to_mword perms in 
    let mask : (mword 64) := zero_extend perms_mw 64 in
    let mask_inv : (mword 64) := invert_bits mask in 
    let new_cap := with_cap c (mword_to_bv (CapClearPerms (bv_to_mword c.(cap)) mask_inv)) in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.

  Definition cap_clear_global_perm (cap:t) : t := 
    cap_narrow_perms cap (list_bool_to_bv (Permissions.make_permissions [Permissions.Global_perm])).

  Definition cap_set_bounds (c : t) (bounds : Bounds.t) (exact : bool) : t :=
    (* CapSetBounds sets the lower bound to the value of the input cap,
       so we first have to set the value of cap to bounds.base. *)
    let '(base,limit) := bounds in
    let base_as_val : AddressValue.t := bv_to_bv base in  
    let new_cap := cap_set_value c base_as_val in 
    let req_len : (mword (Z.of_N Bounds.bound_len)) := 
      mword_of_int (Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base)) in 
    let new_cap := 
      with_cap new_cap (mword_to_bv (CapSetBounds (bv_to_mword new_cap.(cap)) req_len exact)) in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.

  Definition cap_narrow_bounds (cap : t) (bounds : Bounds.t) : t :=
    cap_set_bounds cap bounds false.

  Definition cap_narrow_bounds_exact (cap : t) (bounds : Bounds.t) : t :=
    cap_set_bounds cap bounds true.

  Definition cap_is_valid (c:t) : bool := Bool.eqb (CapIsTagClear (bv_to_mword c.(cap))) false.

  Definition cap_is_invalid (cap:t) : bool := negb (cap_is_valid cap).
    
  Definition cap_is_unsealed (cap:t) : bool := negb (cap_is_sealed cap).
  
  Definition cap_is_in_bounds (c:t) : bool := CapIsInBounds (bv_to_mword c.(cap)).

  Definition cap_is_not_in_bounds (cap:t) : bool := negb (cap_is_in_bounds cap).  
  
  Definition cap_is_exponent_out_of_range (c:t) : bool :=
    CapIsExponentOutOfRange (bv_to_mword c.(cap)).

  Definition cap_has_perm (cap:t) :=
    let perms : (mword 64) := zero_extend (bv_to_mword (cap_get_perms cap)) 64 in 
    fun perm => CapPermsInclude perms perm.

  Definition cap_has_seal_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_SEAL.

  Definition cap_has_unseal_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_UNSEAL.

  Definition cap_has_global_perm (cap:t) : bool := cap_has_perm cap CAP_PERM_GLOBAL.

  Definition cap_seal (cap : t) (k : t) : t :=
    let key : ObjType.t := (cap_get_value k) in 
    let sealed_cap := cap_set_objtype cap key in 
    if (cap_is_valid cap) && (cap_is_valid k) && 
       (cap_is_unsealed cap) && (cap_is_unsealed k) && 
       (cap_has_seal_perm k) && (cap_is_in_bounds k) &&
       (Z.to_N (bv_to_Z_unsigned key) <=? ObjType.CAP_MAX_OBJECT_TYPE)%N then 
       sealed_cap
    else
       cap_invalidate sealed_cap.

  Definition cap_unseal (sealed_cap:t) (unsealing_cap:t) : t :=
    let value := cap_get_value unsealing_cap in 
    let key := cap_get_obj_type sealed_cap in 
    let unsealed_sealed_cap := 
      with_cap sealed_cap (mword_to_bv (CapUnseal (cap_to_mword sealed_cap))) in 
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

  Definition cap_seal_immediate (cap : t) (seal_ot : ObjType.t) 
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
    mword_to_Z_unsigned (CapGetRepresentableMask (@mword_of_int (Z.of_N AddressValue.len) len)).

  (* Will need to see how this compares with Microsoft's Small Cheri 
  (Technical report coming up -- as of Oct 24 2022) *)
  Definition representable_length (len : Z) : Z :=
    let mask:Z := representable_alignment_mask len in
    let nmask:Z := AddressValue.bitwise_complement_Z mask in
    let result:Z := Z.land (Z.add len nmask) mask in 
      result.

  Definition make_cap (value : AddressValue.t) (otype : ObjType.t) (bounds : Bounds.t) (perms : Permissions.t) : t :=
    let new_cap := cap_cU () in 
    let perms_to_keep := list_bool_to_bv ((bv_to_list_bool perms)) in 
    let new_cap := cap_narrow_perms new_cap perms_to_keep in 
    let new_cap := cap_narrow_bounds new_cap bounds in 
    let new_cap := cap_set_value new_cap value in 
      cap_set_objtype new_cap otype.
    
  (* Should we check that size is not too large? *)
  Definition alloc_cap (a_value : AddressValue.t) (size : AddressValue.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_UNSEALED 
      (Bounds.of_Zs (bv_to_Z_unsigned a_value, Z.add (bv_to_Z_unsigned a_value) (bv_to_Z_unsigned size)))
      (Permissions.perm_alloc).
    
  Definition alloc_fun (a_value : AddressValue.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_RB 
      (Bounds.of_Zs (bv_to_Z_unsigned a_value, Z.succ (Z.succ (bv_to_Z_unsigned a_value)))) 
      Permissions.perm_alloc_fun.

  Definition value_compare (cap1 cap2 : t) : comparison :=
    if (cap_get_value cap1 =? cap_get_value cap2)%stdpp then Eq
    else if (cap_get_value cap1 <? cap_get_value cap2) then Lt
    else Gt.

  Definition exact_compare (cap1 cap2 : t) : comparison :=
    if (cap1.(cap) =? cap2.(cap)) then Eq 
    else if (cap1.(cap) <? cap2.(cap)) then Lt 
    else Gt.

  Definition cap_ptraddr_representable (c : t) (a : AddressValue.t) : bool :=
    CapIsRepresentable (bv_to_mword c.(cap)) (bv_to_mword a).
  
  Definition cap_bounds_representable_exactly (cap : t) (bounds : Bounds.t) : bool :=
    let '(base, limit) := bounds in
    let len := Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base) in
    let base' : (bv AddressValue.len) := 
      Z_to_bv AddressValue.len (bv_to_Z_unsigned base) in 
    let len' := mword_of_int (len:=Z.of_N Bounds.bound_len) len in 
    let new_cap : t := cap_set_value cap base' in
    let new_cap : (mword _) := CapSetBounds (cap_to_mword new_cap) len' true in
    CapIsTagSet new_cap.

  Definition cap_bounds_check (cap:t) (bounds : Bounds.t) : bool :=
    let '(base, limit) := bounds in
    let len := Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base) in
    let base' : (bv AddressValue.len) := 
      AddressValue.of_Z (bv_to_Z_unsigned base) in 
    let len' := mword_of_int (len:=Z.of_N Bounds.bound_len) len in 
    CapIsRangeInBounds (cap_to_mword cap) (bv_to_mword base') len'.

  Definition cap_is_null_derived (c : t) : bool :=
    let a := cap_get_value c in
    let c0 := cap_c0 () in
    let c' := cap_set_value c0 a in
    c.(cap) =? c'.(cap).
    
  (* Extracted from https://github.com/vzaliva/cerberus/blob/master/coq/Utils.v *)  
  Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
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

  Definition encode (isexact : bool) (c : t) : option ((list ascii) * bool) :=
    let tag : bool := cap_is_valid c in 
    let cap_bits := bits_of (bv_to_mword c.(cap)) in 
    let w : (mword _) := vec_of_bits (List.tail cap_bits) in
    match mem_bytes_of_bits w with
    | Some bytes =>
        match try_map memory_byte_to_ascii bytes with
        | Some chars => Some (chars, tag)
        | None => None
        end
    | None => None
    end.

  Definition decode (bytes : list ascii) (tag : bool) : option t :=
    if Nat.eq_dec (List.length bytes) 16%nat then
      let bytes := List.rev bytes in (* TODO: Delete this? *)
      let bits : (list bool) := tag::(bool_bits_of_bytes bytes) in
      let bitsu := List.map bitU_of_bool bits in
      let w : (mword _) := vec_of_bits bitsu in
      (* Some (mword_to_bv w) *) (* This requires the proof below, but makes tests harder *)
      let z : Z := mword_to_Z_unsigned w in 
      let c : option cap_t := Z_to_bv_checked Capability.len z in 
      match c with 
        Some c => Some (cap_t_to_t c Default_CapGhostState)
      | None   => None
      end
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

  Definition eqb_cap (cap1:cap_t) (cap2:cap_t) : bool := (cap1 =? cap2)%stdpp.
    
  Definition eqb (cap1:t) (cap2:t) : bool := eqb_cap cap1.(cap) cap2.(cap).

  Definition is_sentry (c : t) : bool :=
    match cap_get_seal c with
    | SealType.Cap_SEntry => true
    | _ => false
    end.
    
  Definition flags_as_str (c:t): string :=
    let attrs :=
      let a (f:bool) s l := if f then s::l else l in
      let gs := (get_ghost_state c).(tag_unspecified) in
        a gs "notag"
          (a (andb (negb (cap_is_valid c)) (negb gs)) "invalid"
             (a (is_sentry c) "sentry"
                (a ((negb (is_sentry c)) && cap_is_sealed c) "sealed" [])))
      in
    if Nat.eqb (List.length attrs) 0%nat then ""
    else " (" ++ String.concat "," attrs ++ ")".

  Definition to_string_pretty (c:t) : string :=
    AddressValue.to_string (cap_get_value c) ++ " [" ++ Permissions.to_string (cap_get_perms c) ++ "," ++ Bounds.to_string (cap_get_bounds c) ++ "]".

  Definition to_string_pretty_2 (c:t) : string :=
    if cap_is_null_derived c then
      AddressValue.to_string (cap_get_value c)
    else
      (AddressValue.to_string (cap_get_value c)) ++ " " ++ "[" ++
        (if (get_ghost_state c).(bounds_unspecified)
         then "?-?"
         else
           Permissions.to_string (cap_get_perms c) ++ "," ++
           Bounds.to_string (cap_get_bounds c)  )
        ++ "]" ++
        (flags_as_str c).

  Definition to_string_full (c:t) : string :=
    HexString.of_Z (bv_to_Z_unsigned c.(cap)). 

  Definition to_string (c:t) : string :=
    (* to_string_full c ++ ": " ++  *)
    to_string_pretty_2 c.

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

  (* Lemma for eqb on capabilities directly without the ghoststate record.
  Lemma eqb_value_compare: forall a b, eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: a = b).
    { unfold eq in H. 
        rewrite -> Z.eqb_eq in H. 
        apply bv_eq. 
        apply H. }
        rewrite <- P. unfold value_compare. unfold eq. rewrite Z.eqb_refl. reflexivity. Qed. *)  

  Lemma eqb_value_compare: forall (a b : t), eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: (cap a) = (cap b)). (* or just apply Lemma eqb_cap_value_compare *)
    { unfold eqb_cap in H. unfold Morello.eqb in H. rewrite -> Z.eqb_eq in H. 
      apply bv_eq. apply H. }
    unfold value_compare. unfold cap_get_value.
    rewrite <- P. unfold Morello.eqb.
    rewrite Z.eqb_refl. reflexivity. Qed.
  
  
  (* Lemma for eqb on capabilities directly without the ghoststate record.
  Lemma eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb. unfold exact_compare. destruct (a =? b).
      + reflexivity.
      + destruct (b >? a). 
        { discriminate. } { discriminate. }
    Qed. *)

  Lemma eqb_exact_compare: forall (a b : t), eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold eqb_cap. unfold exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb. unfold eqb_cap. unfold exact_compare. destruct (cap a =? cap b).
      + reflexivity.
      + destruct (cap a <? cap b). 
        { discriminate. } { discriminate. }
    Qed.
        
End Capability.  


Module TestCaps.

  (* Import MorelloCapability. *)

  (* c1 corresponds to https://www.morello-project.org/capinfo?c=1900000007f1cff1500000000ffffff15 *)
  Definition c1:Capability.t := Capability.of_Z 0x1900000007f1cff1500000000ffffff15.
  Definition c1_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat 
    [0x15;0xff;0xff;0xff;0;0;0;0;0x15;0xff;0x1c;0x7f;0;0;0;0x90]).

  (* c2 corresponds to https://www.morello-project.org/capinfo?c=1d800000066f4e6ec00000000ffffe6ec *)
  Definition c2:Capability.t := Capability.of_Z 0x1d800000066f4e6ec00000000ffffe6ec.
  Definition c2_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat (
    List.rev [0xd8;0x00;0x00;0x00;0x66;0xf4;0xe6;0xec;0x00;0x00;0x00;0x00;0xff;0xff;0xe6;0xec])).

  (* c3 corresponds to https://www.morello-project.org/capinfo?c=1dc00000066d4e6d02a000000ffffe6d0 *)
  Definition c3_bytes := ["208"%char;"230"%char;"255"%char;"255"%char;"000"%char;"000"%char;"000"%char;
    "042"%char;"208"%char;"230"%char;"212"%char;"102"%char;"000"%char;"000"%char;"000"%char;"220"%char].
  
End TestCaps.
