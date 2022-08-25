(* Coq formalization on CHERI Capablities *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Sets.Ensembles.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Notation vector := VectorDef.t.

Open Scope nat_scope.
Open Scope list_scope.

Section Interval.
  Variable V:Type.
  Variable V_lt: V -> V -> Prop.
  Variable V_lt_irref: forall a, ~ V_lt a a.

  Local Notation "x < y"  := (V_lt x y).
  Local Notation "x <= y" := (V_lt x y \/ x=y).

  Inductive Interval : Type :=
  | Incl_Interval (base top:V): (base <= top) -> Interval (* inclusive *)
  | Empty_Interval (base:V): Interval. (* empty with base *)

  (* [<=] relation on intervals *)
  Definition interval_leq: relation (Interval) :=
    fun i1 i2 =>
      match i1, i2 with
      | Empty_Interval b1, Empty_Interval b2 => b1 = b2
      | @Incl_Interval b1 t1 _, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ t1 <= t2
      | Empty_Interval b1, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ b1 <= t2
      | @Incl_Interval b1 t1 _, Empty_Interval b2 =>  False
      end.

End Interval.
Arguments Incl_Interval {V}%type_scope {V_lt}%type_scope.
Arguments Empty_Interval {V}%type_scope {V_lt}%type_scope.

Declare Scope IntervalScope.
Delimit Scope IntervalScope with interval.
Notation "x <= y" := (interval_leq x y) : IntervalScope.

Open Scope IntervalScope.

Class CAddress (A:Type) :=
  {
  (* "less than" *)
  address_lt: relation A;
  address_lt_irref: forall a, ~ address_lt a a;

  (* Generates of set of addresses in the given range. *)
  addresses_in_interval: (Interval address_lt) -> Ensemble A;
  }.

Section CAddressProperties.
  Context `{ADR: CAddress A}.

  (* address interval. *)
  Definition address_interval := Interval address_lt.

  (* Set of addresses type alias *)
  Definition address_set := Ensemble A.

  (* Set membership predicate *)
  Definition address_set_in (a:A) (xs:address_set) : Prop
    := In _ xs a.

  (* Empty address set constant *)
  Definition empty_address_set: address_set := Empty_set A.

  (* "less of equal" relation on on addresses *)
  Definition address_le: relation A :=
    fun a b => address_lt a b \/ a = b.

End CAddressProperties.

Class CPermission (P:Type) :=
  {

  (* Number of user-defined flags *)
  USER_PERMS_LEN: nat ;

  (* Convenience functions to examine some permission bits *)
  global: P -> Prop; (* it permssion in RISV but in Morello spec while it is
                    encoded and treated as one, it is sigled out as separate
                    field of logical Capability structure (see R_HRVBQ paragraph
                    in Morello spec. *)
  permits_execute: P -> Prop;
  permits_ccall: P -> Prop;
  permits_load: P -> Prop;
  permits_load_cap: P -> Prop;
  permits_seal: P -> Prop;
  permits_store: P -> Prop;
  permits_store_cap: P -> Prop;
  permits_store_local_cap: P -> Prop;
  permits_system_access: P -> Prop;
  permits_unseal: P -> Prop;

  (* User-defined permissions *)
  user_perms: P -> vector bool USER_PERMS_LEN;

  }.

Section PermissinProperties.
  Context `{ADR: CAddress A}
          `{PERM: @CPermission P}.

  (* Logical comparison ofpermssions based solely on their properties
     expressed in [Permissoin] typeclass interface.  Underlying
     implementation type may have some additional fields not
     considered here *)
  Definition perms_eq (p1 p2: P): Prop :=
    (global p1         ) = (global p2) /\
    (permits_execute p1         ) = (permits_execute p2) /\
    (permits_ccall p1           ) = (permits_ccall p2) /\
    (permits_load p1            ) = (permits_load p2) /\
    (permits_load p1            ) = (permits_load p2) /\
    (permits_seal p1            ) = (permits_seal p2) /\
    (permits_store p1           ) = (permits_store p2) /\
    (permits_store_cap p1       ) = (permits_store_cap p2) /\
    (permits_store_local_cap p1 ) = (permits_store_local_cap p2) /\
    (permits_system_access p1   ) = (permits_system_access p2) /\
    (permits_unseal p1          ) = (permits_unseal p2) /\
    (user_perms p1              ) = (user_perms p2)
  .

  Definition user_perms_leq: relation (vector bool USER_PERMS_LEN)
    := VectorDef.Forall2 Bool.le.


  (* Logical "lessn than" comparison of permssions based solely on
     their properties expressed in [Permissoin] typeclass
     interface.  Underlying implementation type may have some
     additional fields not considered here *)
  Definition perms_leq (p1 p2: P): Prop :=
    ((global p1         ) -> (global p2)) /\
    ((permits_execute p1         ) -> (permits_execute p2)) /\
    ((permits_ccall p1           ) -> (permits_ccall p2)) /\
    ((permits_load p1            ) -> (permits_load p2)) /\
    ((permits_load p1            ) -> (permits_load p2)) /\
    ((permits_seal p1            ) -> (permits_seal p2)) /\
    ((permits_store p1           ) -> (permits_store p2)) /\
    ((permits_store_cap p1       ) -> (permits_store_cap p2)) /\
    ((permits_store_local_cap p1 ) -> (permits_store_local_cap p2)) /\
    ((permits_system_access p1   ) -> (permits_system_access p2)) /\
    ((permits_unseal p1          ) -> (permits_unseal p2)) /\
    user_perms_leq (user_perms p1) (user_perms p2)
  .

End PermissinProperties.

Class CObjectType (OT:Type)
  :=
    {
    }.

Section CapabilityDefinition.
  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress}
          `{PERM: @CPermission P}.

  (*
     Related docs:
     - UCAM-CL-TR-951.pdf appendix D.9
   *)
  Variant CapSeal :=
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  | Cap_Indirect_SEntry_Pair (* "LBP" in Morello *)
  | Cap_Sealed (otype:OT).

  Variant CapValue :=
  | CapAddress (a:A)
  | CapToken (ot:OT).

  (* Capability data type *)
  Class CCapability (C:Type) :=
    {

    (* Number of user-defined flags *)
    CAP_FLAGS_LEN: nat ;

    (* Returns either inclusive bounds for covered
     memory region *)
    get_bounds: C -> address_interval;

    get_perms: C -> P;

    (* Previously "get_cursor" *)
    get_value: C -> CapValue;

    (* Get informaiton about "seal" on this capability *)
    get_seal: C -> CapSeal;

    (* user-defined flags *)
    get_flags: C -> vector bool CAP_FLAGS_LEN;

    (* Boldly assuming this one never fails *)
    address_of_otype: OT -> A;

    (* NULL capability *)
    C0 : C ;
    (* Syncing permissoins with value *)

    seal_perms_value_type:
      forall c, (permits_seal (get_perms c) \/ permits_unseal (get_perms c))
           <->
           exists t, get_value c = CapToken t;

    (* --- Represetability Checks ---- *)

    (* Due to encoding, not all capabilities with large bounds have a
       contiguous representable region. This representability check is
       applied when manipulating a Capability Value

       For example, in Morello: if modifying a Capability Value causes
       the bounds to change, a representabilty check fails. Some
       versions of the check may fail in additional cases.

       See: `CapIsRepresentable` in Morello *)

    addr_representable: C -> A -> Prop;

    (* Whenever given bounds could be encoded exactly. Due to
       encoding issues not all bounds could be reprsented exactly
       (e.g. due to alignment).

       See: `CapIsRepresentable` in Morello *)
    bounds_representable_exactly: C -> address_interval -> Prop;

    }.

  (* Operations on capabilities.

     See also:
     - Section "2.6 Manipulating Capabilities" in Morello spec.
   *)
  Class CCapabilityOps (C:Type) `{CAPS:CCapability C} :=
    {

    (* --- Monotonic manipulation -- *)

    (* Modifying the Capability Value (address of object type)

       Related instructions:
       - CFromPtr in RISC V
       - CSetAddr in RISC V
       - SCVALUE in Morello
       - CCopyType in RISC V
       - CPYTYPE in Morello
     *)
    set_value: C -> CapValue -> C;

    (* Reducing the Capability Bounds (with rounding)

       Related instructions:
       - CSetBounds in RISCV
       - SCBNDS (immediate) in Morello?
     *)
    narrow_bounds: C -> address_interval -> C;

    (* Reducing the Capability Bounds (exact)

       Related instructions:
       - CSetBoundsExact in RISCV
       - SCBNDSE (immediate) in Morello?
     *)
    narrow_bounds_exact: C -> address_interval -> C;

    (* Reducing the Capability Permissions

       Related instructions:
       - CAndPerm in RISC V
       - CLRPERM in Morello
     *)
    narrow_perms: C -> P -> C ;

    (* Sealing operations *)

    (* Regular sealing (with object type)

       Related instructions:
       - CSeal in RISC V.
       - SEAL (capabilitiy) in Morello
     *)
    seal: C -> C -> C;

    (* Seal Entry
       - CSealEntry in RISC V.
       - SEAL (immediatete) in Morello
     *)
    seal_entry: C -> C;

    (* Seal Indirect Entry
       - CInvokeInd proposed but not implmented RISC V
       - SEAL (immediatete) in Morello
     *)
    seal_indirect_entry: C -> C;

    (* Seal Entry Pair
       - proposed but not implmented in in RISC V.
       - SEAL (immediatete) in Morello
     *)
    seal_indirect_entry_pair: C -> C;

    (* Modifying the Capability Flags
       - BICFLGS in Morello
       - EORFLGS in Morello
       - ORRFLGS in Morello
       - SCFLGS in Morello
     *)
    set_flags: C -> vector bool CAP_FLAGS_LEN -> C;

    (* --- Controlled non-monotonic manipulation --  *)

    (* Unsealing a capability using an unsealing operation.
       - CUnseal in RISCV
       - UNSEAL in Morello
     *)
    unseal: C -> C -> C;

    (* TODO: Using a permitted, privileged capability creating
       instruction to mark a register or memory location as holding a valid
       capability *)

    }.

End CapabilityDefinition.

Section CCapabilityProperties.

  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress A}
          `{PERM: @CPermission P}
          `{CAPS: @CCapability OT A ADR P PERM C}
          `{COPS: @CCapabilityOps OT A ADR P PERM C CAPS}.

  (* Helper function to get address *)
  Definition get_address (c:C) : A :=
    match get_value c with
    | CapAddress a => a
    | CapToken t => address_of_otype t
    end.

  (* Helper function to check if capability is sealed (with any kind of seal) *)
  Definition is_sealed (c:C) : Prop
    := match get_seal c with
       | Cap_Unsealed => False
       | _ => True
       end.

  (* Helper function to check if sealed entry capability *)
  Definition is_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_SEntry => True
       | _ => False
       end.

  (* Helper function to check if indirect entry capability *)
  Definition is_indirect_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_Indirect_SEntry => True
       | _ => False
       end.

  (* Helper function to check if indirect entry capability *)
  Definition is_indirect_sentry_pair (c:C) : Prop
    := match get_seal c with
       | Cap_Indirect_SEntry_Pair => True
       | _ => False
       end.

  (* Return [None] it the capability is "unsealed" and
     [Some OT] otherwise *)
  Definition get_obj_type (c:C): option OT
    := match get_seal c with
       | Cap_Sealed otype => Some otype
       | _ => None
       end.

  (* Set of cap type alias *)
  Definition cap_set := Ensemble C.

  Definition cat_set_in (x:C) (cs:cap_set) : Prop
    := In _ cs x.

  Definition get_mem_region (c:C): address_set
    := addresses_in_interval (get_bounds c).

  (* "<=" relation on bounds *)
  Definition bounds_leq: relation C :=
    fun c1 c2 => interval_leq (get_bounds c1) (get_bounds c2).

  Definition flags_leq: relation (vector bool CAP_FLAGS_LEN)
    := VectorDef.Forall2 Bool.le.

  (* "<=" relation on Capabilities *)
  Definition cap_leq: relation C :=
    fun c1 c2 =>
      c1 = c2
      \/ (~ is_sealed c1 /\ ~ is_sealed c2
         /\ bounds_leq c1 c2
         /\ flags_leq (get_flags c1) (get_flags c2)
         /\ perms_leq (get_perms c1) (get_perms c2)).

  Declare Scope CapScope.
  Delimit Scope CapScope with cap.

  Local Notation "x <= y" := (cap_leq x y) : CapScope.

  (* TODO: This is unused for now *)
  Definition invokable (cc cd: C): Prop:=
    let pc := get_perms cc in
    let pd := get_perms cd in
    is_sealed cc /\ is_sealed cd /\
    ~ is_sentry cc /\ ~ is_sentry cd /\
    (* TODO: what about indirect sentry? *)
    permits_ccall pc /\ permits_ccall pd /\
    get_obj_type cc = get_obj_type cd /\
    permits_execute pc /\ ~ permits_execute pd.

  Definition CapIsInBounds(c:C): Prop
    := address_set_in (get_address c) (get_mem_region c).

  (* Transition function between valid Capabilities state space *)
  Inductive CapStateStep (c:C) : C -> Prop  :=
  | SetValue (v:CapValue):
      match v with
      | CapAddress a =>
        (~permits_seal (get_perms c) /\ ~permits_unseal (get_perms c)) ->
        addr_representable c a
      | CapToken t =>
        permits_seal (get_perms c) \/ permits_unseal (get_perms c)
      end
      ->
      CapStateStep c (set_value c v)
  | NarrowBounds (b:address_interval):
      ~ is_sealed c ->
      (b <= (get_bounds c))%interval
      ->
      CapStateStep c (narrow_bounds c b)
  | NarrowBoundsExact (b:address_interval):
      ~ is_sealed c ->
      (b <= (get_bounds c))%interval ->
      bounds_representable_exactly c b
      ->
      CapStateStep c (narrow_bounds_exact c b)
  | NarrowPerms (p:P):
      CapStateStep c (narrow_perms c p)
  | SetFlags (f:vector bool CAP_FLAGS_LEN):
      CapStateStep c (set_flags c f)
  | Seal (k:C):
      ~ is_sealed c ->
      ~ is_sealed k ->
      permits_seal (get_perms k) ->
      CapIsInBounds k
      ->
      CapStateStep c (seal c k)
  | SealEntry:
      CapStateStep c (seal_entry c)
  | SealIndirectEntry:
      CapStateStep c (seal_indirect_entry c)
  | SealIndirectEntryPair:
      CapStateStep c (seal_indirect_entry_pair c)
  | UnSeal (k:C):
      is_sealed c ->
      ~ is_sealed k ->
      permits_unseal (get_perms k) ->
      CapIsInBounds k ->
      (exists ot,
          get_value k = CapToken ot /\
          get_obj_type c = Some ot)
      ->
      CapStateStep c (unseal c k)
  .

  Inductive derivable (cs:cap_set) : cap_set :=
  | DerivableIn: forall c, cat_set_in c cs -> derivable cs c
  | DerivableStep: forall c c', derivable cs c ->
                           CapStateStep c c' ->
                           derivable cs c'.

  Local Notation "x ⊆ y" := (Included _ x y) (at level 61, right associativity).
  Local Notation "x ∪ y" := (Union _ x y) (at level 61, right associativity).
  Local Notation "x ∩ y" := (Intersection _ x y) (at level 61, right associativity).

  (* "Monotonicity" property *)
  Lemma derivable_mono:
    forall cs cs', cs ⊆ cs' -> derivable cs ⊆ derivable cs'.
  Proof.
    intros cs cs' H c IN.
    induction IN.
    -
      apply DerivableIn.
      unfold cat_set_in in *.
      auto.
    -
      eapply DerivableStep; eauto.
  Qed.

  (* "Extensive" property (as in closure operators).
     Formely known as "derivable_refl".
   *)
  Lemma derivable_extensive:
    forall cs, cs ⊆ derivable cs.
  Proof.
    intros cs c H.
    constructor 1.
    apply H.
  Qed.

  (* idempotentence property *)
  Lemma derivable_idemp:
    forall cs, derivable (derivable cs) = derivable cs.
  Proof.
    intros cs.
    apply Extensionality_Ensembles.
    split.
    -
      intros x H.
      induction H; unfold cat_set_in, In in *.
      + auto.
      + eapply DerivableStep; eauto.
    -
      intros x H.
      induction H; unfold cat_set_in, In in *.
      + apply DerivableIn.
        apply DerivableIn.
        assumption.
      + eapply DerivableStep; eauto.
  Qed.

  Lemma derivable_empty: derivable empty_address_set = empty_address_set.
  Proof.
    unfold empty_address_set.
    apply Extensionality_Ensembles.
    unfold Same_set, Included.
    split; intros.
    -
      unfold In in H.
      induction H.
      + apply Noone_in_empty in H; tauto.
      + apply Noone_in_empty in IHderivable; tauto.
    -
      apply Noone_in_empty in H; tauto.
  Qed.

  Lemma derivable_union_subseteq_absorb:
    forall cs cs',
      cs' ⊆ derivable cs ->
      derivable (cs ∪ cs') = derivable cs.
  Proof.
    intros cs cs' H.
    apply Extensionality_Ensembles.
    split.
    -
      intros c H0.
      induction H0.
      +
        apply Union_inv in H0.
        destruct H0.
        *
          apply DerivableIn, H0.
        *
          specialize (H c).
          apply H, H0.
      + eapply DerivableStep; eauto.
    -
      apply derivable_mono.
      intros x H0.
      apply Union_introl.
      auto.
  Qed.

  (* Formely known as "derivable_Int1_subset" *)
  Lemma derivable_IntL_subset:
    forall a b, derivable (a ∩ b) ⊆ derivable a.
  Proof.
    intros a b.
    apply derivable_mono.
    unfold Included.
    intros c H.
    apply Intersection_inv in H.
    apply H.
  Qed.

  (* Formely known as "derivable_Int2_subset" *)
  Lemma derivable_IntR_subset:
    forall a b, derivable (a ∩ b) ⊆ derivable b.
  Proof.
    intros a b.
    apply derivable_mono.
    unfold Included.
    intros c H.
    apply Intersection_inv in H.
    apply H.
  Qed.

End CCapabilityProperties.
