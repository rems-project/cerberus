Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.HexString.
Require Import Coq.ZArith.Zdigits.
Require Import Coq.Bool.Bool.

From SailStdpp Require Import Values Operators_mwords.

From CheriCaps.Morello Require Import CapFns Capabilities.
From CheriCaps.Common Require Import Utils Capabilities.

Require Import CapabilitiesGS.

Import ListNotations.

Module MorelloCaps := CheriCaps.Morello.Capabilities.


Module Capability_GS <: CAPABILITY_GS (MorelloCaps.AddressValue) (MorelloCaps.Flags) (MorelloCaps.ObjType) (MorelloCaps.SealType) (MorelloCaps.Bounds) (MorelloCaps.Permissions).
  Definition cap_t := MorelloCaps.Capability.t.

  Inductive morello_cap_t :=
  {
    cap : cap_t;
    ghost_state: CapGhostState
  }.
	
	Definition t := morello_cap_t.

  (** ghost state management **)
  Definition get_ghost_state (c:t) := c.(ghost_state).
  Definition set_ghost_state (c:t) gs := {| cap := c.(cap); ghost_state := gs |}.
  
  Definition cap_t_to_t (c:cap_t) (gs:CapGhostState) : t := 
    {| cap := c; ghost_state := gs |}.

  (* Sets the cap:cap_t in c:t to the given cap_ *)
  Definition set_cap (c:t) (cap_:cap_t) : t :=
    {| cap := cap_; ghost_state := get_ghost_state c |}.

  (* Wraps cap:cap_t with the default ghost state *)
  Definition add_gs (cap:cap_t) : t := 
    cap_t_to_t cap Default_CapGhostState.
    
  Definition of_Z (z:Z) : t := cap_t_to_t (Capability.of_Z z) Default_CapGhostState.
     
  Definition sizeof_ptraddr := Capability.sizeof_ptraddr. (* in bytes *)
  Definition sizeof_cap := Capability.sizeof_cap. (* in bytes *)
  Definition min_ptraddr := Capability.min_ptraddr.
  Definition max_ptraddr := Capability.max_ptraddr.

  Definition cap_c0 (u:unit) : t := 
    cap_t_to_t (Capability.cap_c0 u) Default_CapGhostState.

  Definition cap_get_value (c:t) : AddressValue.t := 
    Capability.cap_get_value (c.(cap)).
  
  Definition cap_get_obj_type (c:t) : ObjType.t := 
    Capability.cap_get_obj_type (c.(cap)).
  
  Definition cap_get_bounds (c:t) : Bounds.t :=
    Capability.cap_get_bounds (c.(cap)).
  
  Definition cap_get_offset (c:t) : Z :=
    Capability.cap_get_offset (c.(cap)).
        
  Definition cap_get_seal (c:t) : SealType.t := 
    Capability.cap_get_seal (c.(cap)).
    
  (* The flags are the top byte of the value. *)
  Program Definition cap_get_flags (c:t) : Flags.t := 
    Capability.cap_get_flags (c.(cap)).

  Definition cap_get_perms (c:t) : Permissions.t := 
    Capability.cap_get_perms (c.(cap)).

  Definition cap_is_sealed (c:t) : bool :=
    Capability.cap_is_sealed (c.(cap)).
  
  Definition cap_invalidate (c:t) : t := 
    set_cap c (Capability.cap_invalidate c.(cap)).

  Definition cap_set_value (c:t) (value:AddressValue.t) : t :=
    set_cap c (Capability.cap_set_value c.(cap) value).
  
  Definition cap_set_flags (c:t) (f: Flags.t) : t :=
    set_cap c (Capability.cap_set_flags c.(cap) f).
  
  Definition cap_set_objtype (c:t) (ot:ObjType.t) : t :=
    set_cap c (Capability.cap_set_objtype c.(cap) ot).

  (* [perms] must contain [1] for permissions to be kept and [0] for those to be cleared *)
  Definition cap_narrow_perms (c:t) (perms:Permissions.t) : t :=
    set_cap c (Capability.cap_narrow_perms c.(cap) perms).

  Definition cap_narrow_bounds (c : t) (bounds : Bounds.t) : t :=
    set_cap c (Capability.cap_narrow_bounds c.(cap) bounds).

  Definition cap_narrow_bounds_exact (c : t) (bounds : Bounds.t) : t :=
    set_cap c (Capability.cap_narrow_bounds_exact c.(cap) bounds).

  Definition cap_is_valid (c:t) : bool := Capability.cap_is_valid c.(cap).

  Definition cap_is_invalid (c:t) : bool := Capability.cap_is_invalid c.(cap).
    
  Definition cap_is_in_bounds (c:t) : bool := Capability.cap_is_in_bounds c.(cap).

  Definition cap_seal (c : t) (sealing_c : t) : t :=
    set_cap c (Capability.cap_seal c.(cap) sealing_c.(cap)).

  Definition cap_unseal (sealed_c:t) (unsealing_c:t) : t :=
    set_cap sealed_c (Capability.cap_unseal sealed_c.(cap) unsealing_c.(cap)).

  (* For sealing with RB *)
  Definition cap_seal_entry (c:t) : t := set_cap c (Capability.cap_seal_entry c.(cap)).

  (* For sealing with LB *)
  Definition cap_seal_indirect_entry (c:t) : t := 
    set_cap c (Capability.cap_seal_indirect_entry c.(cap)).

  (* For sealing with LPB *)  
  Definition cap_seal_indirect_entry_pair (c:t) : t := 
    set_cap c (Capability.cap_seal_indirect_entry_pair c.(cap)).

  Definition representable_alignment_mask (len:Z) : Z :=
    Capability.representable_alignment_mask len.

  Definition representable_length (len : Z) : Z :=
    Capability.representable_length len.

  Definition alloc_cap (a_value : AddressValue.t) (size : AddressValue.t) : t :=
    add_gs (Capability.alloc_cap a_value size).
    
  Definition alloc_fun (a_value : AddressValue.t) : t :=
    add_gs (Capability.alloc_fun a_value).

  Definition value_compare (cap1 cap2 : t) : comparison :=
    Capability.value_compare (cap1.(cap)) (cap2.(cap)).

  Definition exact_compare (cap1 cap2 : t) : comparison :=
    Capability.exact_compare (cap1.(cap)) (cap2.(cap)).

  Definition cap_ptraddr_representable (c : t) (a : AddressValue.t) : bool :=
    Capability.cap_ptraddr_representable (c.(cap)) a.
  
  Definition cap_bounds_representable_exactly (c : t) (bounds : Bounds.t) : bool :=
    Capability.cap_bounds_representable_exactly (c.(cap)) bounds.

  Definition cap_bounds_check (c:t) (bounds : Bounds.t) : bool :=
    Capability.cap_bounds_check (c.(cap)) bounds.

  Definition cap_is_null_derived (c : t) : bool :=
    Capability.cap_is_null_derived c.(cap).
    
  Definition encode (c : t) : option ((list ascii) * bool) :=
    Capability.encode c.(cap).

  Definition decode (bytes : list ascii) (tag : bool) : option t :=
    match (Capability.decode bytes tag) with 
    | Some c => Some (add_gs c)
    | None   => None 
    end.
  
  Definition eqb_cap (cap1:cap_t) (cap2:cap_t) : bool := Capability.eqb cap1 cap2.
    
  Definition eqb (c1:t) (c2:t) : bool := Capability.eqb c1.(cap) c2.(cap).

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
                (a ((negb (is_sentry c)) && cap_is_sealed c) "sealed" nil)))
      in
    if Nat.eqb (List.length attrs) 0%nat then ""
    else " (" ++ String.concat "," attrs ++ ")".
  
  Definition to_string_pretty (c:t) : string :=
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

  Definition to_string (c:t) : string := to_string_pretty c.

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

  Lemma eqb_value_compare: forall (a b : t), eqb a b = true -> value_compare a b = Eq.
  Proof. intros a b. unfold eqb. unfold value_compare. apply Capability.eqb_value_compare. Qed.
    
  Lemma eqb_exact_compare: forall (a b : t), eqb a b = true <-> exact_compare a b = Eq.
  Proof. intros. unfold eqb. unfold exact_compare. apply Capability.eqb_exact_compare. Qed. 

  Lemma cap_invalidate_invalidates: forall c, cap_is_valid (cap_invalidate c) = false.
  Proof.
    intros c.
    apply Capability.cap_invalidate_invalidates.
  Qed.

  Lemma cap_invalidate_preserves_value: forall c, cap_get_value c = cap_get_value (cap_invalidate c).
  Proof. intros c. apply Capability.cap_invalidate_preserves_value. Qed.

  Lemma cap_get_set_value: forall (c:t) (a:AddressValue.t), cap_get_value (cap_set_value c a) = a.
  Proof. intros. apply Capability.cap_get_set_value. Qed.

  Lemma cap_encode_length:
    forall c l t, encode c = Some (l, t) -> List.length l = sizeof_cap.
  Proof.
    intros.
    eapply Capability.cap_encode_length.
    apply H.
  Qed.

  Lemma cap_exact_encode_decode:
    forall c c' t l, encode c = Some (l, t) -> decode l t = Some c' -> eqb c c' = true.
  Proof.
    intros.
    apply Capability.cap_exact_encode_decode with (t:=t0) (l:=l).
    auto.
    unfold decode in H0.
    destruct (Capability.decode l t0); inversion H0.
    reflexivity.
  Qed.

End Capability_GS.  


Module TestCaps.

  (* c1 corresponds to https://www.morello-project.org/capinfo?c=1900000007f1cff1500000000ffffff15 *)
  Definition c1:Capability_GS.t := Capability_GS.of_Z 0x1900000007f1cff1500000000ffffff15.
  Definition c1_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat 
    [0x15;0xff;0xff;0xff;0;0;0;0;0x15;0xff;0x1c;0x7f;0;0;0;0x90]).

  (* c2 corresponds to https://www.morello-project.org/capinfo?c=1d800000066f4e6ec00000000ffffe6ec *)
  Definition c2:Capability_GS.t := Capability_GS.of_Z 0x1d800000066f4e6ec00000000ffffe6ec.
  Definition c2_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat (
    List.rev [0xd8;0x00;0x00;0x00;0x66;0xf4;0xe6;0xec;0x00;0x00;0x00;0x00;0xff;0xff;0xe6;0xec])).

  (* c3 corresponds to https://www.morello-project.org/capinfo?c=1dc00000066d4e6d02a000000ffffe6d0 *)
  Definition c3_bytes := ["208"%char;"230"%char;"255"%char;"255"%char;"000"%char;"000"%char;"000"%char;
    "042"%char;"208"%char;"230"%char;"212"%char;"102"%char;"000"%char;"000"%char;"000"%char;"220"%char].
  
End TestCaps.
