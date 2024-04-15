Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.ZArith.ZArith_dec.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Decidable.
From Coq.Strings Require Import String Ascii HexString.
Require Import Coq.micromega.Psatz.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Equality. (* for dep. destruction *)
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Require Import bbv.ZLib.

Require Import Lia.

Require Import StructTact.StructTactics.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadLaws MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

From Coq.Lists Require Import List SetoidList. (* after exltlib *)

From CheriCaps.Morello Require Import Capabilities.
From CheriCaps.Common Require Import Capabilities.

From Common Require Import SimpleError Utils ZMap.
From Morello Require Import CapabilitiesGS MorelloCapsGS.

From CheriMemory Require Import CheriMorelloMemory Memory_model CoqMem_common ErrorWithState CoqUndefined ErrorWithState CoqLocation CoqSymbol CoqImplementation CoqTags CoqSwitches CerbSwitches CoqAilTypesAux.

Require Import Tactics.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Require Import AltBinNotations.
Import ListNotations.
Import MonadNotation.

Require Import ProofsAux.

Module Import ZP := FMapFacts.WProperties_fun(Z_as_OT)(ZMap).
Module Import WZP := FMapFacts.WFacts_fun(Z_as_OT)(ZMap).

(* Abstract set of switches *)
Parameter abst_get_switches: unit -> cerb_switches_t.

(* Abstract tag definitions *)
Parameter abst_tagDefs: unit -> (SymMap.t CoqCtype.tag_definition).

Require Import ListSet.

Module AbstTagDefs: TagDefs.
  Definition tagDefs := abst_tagDefs.
End AbstTagDefs.

Lemma sequence_len_errS
  {S E A:Type}
  (s s': S)
  (old : list (errS S E A))
  (new : list A):
  sequence old s = (s', inr new) ->
  List.length old = List.length new.
Proof.
  intros H.
  unfold sequence, mapT, Traversable_list, mapT_list in H.
  unfold Applicative_Monad, Applicative.pure, Monad_errS, ret,
    Applicative.ap, apM, bind, liftM, ret in H.
  cbn in H.
  generalize dependent new.
  revert s s'.
  induction old;intros.
  -
    tuple_inversion.
    reflexivity.
  -
    repeat break_let.
    repeat break_match; repeat tuple_inversion.
    cbn.
    cut (Datatypes.length old = Datatypes.length l0);[lia|].
    subst.
    apply (IHold s0 s').
    auto.
Qed.

(** This is a version where initial and final states are the same and each computation
    is guaranteed to preserve them *)
Lemma sequence_spec_same_state_errS
  {S E A:Type}
  (s : S)
  (old : list (errS S E A))
  (new : list A):
  List.Forall (fun x => exists y, x s = (s, inr y)) old ->
  sequence old s = (s, inr new) ->
  Forall2 (fun m r => m s = (s, inr r)) old new.
Proof.
  intros C H.
  unfold sequence, mapT, Traversable_list, mapT_list in H.
  unfold Applicative_Monad, Applicative.pure, Monad_errS, ret,
    Applicative.ap, apM, bind, liftM, ret in H.
  cbn in H.
  generalize dependent new.
  (* revert C. *)
  induction old;intros.
  -
    tuple_inversion.
    constructor.
  -
    repeat break_let.
    repeat break_match; repeat tuple_inversion.
    cbn.
    assert(s = s0).
    {
      apply Forall_inv in C.
      destruct C.
      rewrite H in Heqp1.
      tuple_inversion.
      reflexivity.
    }
    subst s0.
    constructor.
    +
      assumption.
    +
      apply IHold; clear IHold.
      *
        invc C.
        auto.
      *
        auto.
Qed.

(** This is a more generic version than [sequence_spec_same_state_errS], stating
    that if [sequence] suceeds (returns [inr]) all computations succeed as well.
    It does not make any assumptions or gurarantees about the states *)
Lemma sequence_spec_errS
  {S E A:Type}
  (s s' : S)
  (old : list (errS S E A))
  (new : list A):
  sequence old s = (s', inr new) ->
  Forall2 (fun m r => exists s0 s1, m s0 = (s1, inr r)) old new.
Proof.
  intros H.
  unfold sequence, mapT, Traversable_list, mapT_list in H.
  unfold Applicative_Monad, Applicative.pure, Monad_errS, ret,
    Applicative.ap, apM, bind, liftM, ret in H.
  cbn in H.
  generalize dependent new.
  revert s s'.
  induction old;intros.
  -
    tuple_inversion.
    constructor.
  -
    repeat break_let.
    repeat break_match; repeat tuple_inversion.
    constructor.
    +
      exists s.
      exists s0.
      apply Heqp1.
    +
      eapply IHold.
      eauto.
Qed.

Module RevocationProofs.

  (* --- Memory models instantiated with and without PNVI --- *)

  Definition remove_PNVI: cerb_switches_t -> cerb_switches_t
    :=
    List.filter (fun s => negb (is_PNVI_switch s)).

  Definition remove_Revocation: cerb_switches_t -> cerb_switches_t
    :=
    List.filter (fun s => negb (is_Revocation_switch s)).

  (* --- Equality predicates for types used in Memory Models --- *)

  Import CheriMemoryTypesExe.

  Lemma provenance_eqb_reflexivity:
    forall p, provenance_eqb p p = true.
  Proof.
    intros p.
    destruct p;try reflexivity.
    cbn.
    unfold CheriMemoryTypesExe.storage_instance_id in *.
    lia.
  Qed.

  (* Check whether this cap base address is within allocation *)
  Definition cap_bounds_within_alloc c a : Prop
    :=
    let alloc_base := AddressValue.to_Z a.(base) in
    let alloc_limit := alloc_base + Z.of_nat a.(size) in
    let ptr_base := fst (Bounds.to_Zs (Capability_GS.cap_get_bounds c)) in
    alloc_base <= ptr_base /\ ptr_base < alloc_limit.

  Lemma cap_bounds_within_alloc_dec c a: {cap_bounds_within_alloc c a}+{~cap_bounds_within_alloc c a}.
    pose (alloc_base := AddressValue.to_Z a.(base)).
    pose (alloc_limit := alloc_base + Z.of_nat a.(size)).
    pose (ptr_base := fst (Bounds.to_Zs (Capability_GS.cap_get_bounds c))).
    destruct (Z_le_dec alloc_base ptr_base) as [H1|H1], (Z_lt_dec ptr_base alloc_limit) as [H2|H2].
    - left. split; assumption.
    - right. intro H. apply H2. apply H.
    - right. intro H. apply H1. apply H.
    - right. intro H. destruct H as [H _]. contradiction.
  Qed.

  (* Equality predicate for 2 caps, with additional allocation
     information associated with the 1st one.

     If there is a mismatch between [c1] and [a], we assume that `c1`
     corresponds to a different, now defunct, allocation.  *)
  Inductive cap_match_with_alloc (a: allocation) (c1 c2: Capability_GS.t): Prop
    :=
  | cap_match_alloc_match: cap_bounds_within_alloc c1 a -> c1 = c2 -> cap_match_with_alloc a c1 c2
  | cap_match_with_alloc_mismatch: ~cap_bounds_within_alloc c1 a -> Capability_GS.cap_invalidate c1 = c2 -> cap_match_with_alloc a c1 c2.

  (* This version is restricted to model parametrizations we are
     using. In particular, with PNVI there are no 'dead' allocations,
     they are just removed. Also, without PNVI, instant revocation is
     assumed
   *)
  Inductive single_alloc_id_cap_cmp (allocs: ZMap.t allocation) (alloc_id: Z) c1 c2 : Prop
    :=
  | single_cap_cmp_live:
    (* The allocation ID is mapped to an allocation *)
    forall a, ZMap.MapsTo alloc_id a allocs ->
         cap_match_with_alloc a c1 c2 -> (* then match c1 to c2 based on alloc_id *)
         single_alloc_id_cap_cmp allocs alloc_id c1 c2
  | single_cap_cmp_dead:
    (* The allocation ID is not mapped to an allocation *)
    ~ ZMap.In alloc_id allocs ->
    Capability_GS.cap_invalidate c1 = c2 ->
    single_alloc_id_cap_cmp allocs alloc_id c1 c2.


  (* Equality of byte values without taking provenance into account *)
  Inductive AbsByte_eq: relation AbsByte
    :=
  | AbsByte_no_prov_eq: forall a1 a2,
      copy_offset a1 = copy_offset a2
      /\ value a1 = value a2 -> AbsByte_eq a1 a2.


  Instance AbsByte_Equivalence: Equivalence AbsByte_eq.
  Proof.
    split.
    -
      intros a.
      destruct a.
      constructor.
      split;reflexivity.
    -
      intros a b.
      destruct a, b.
      intros H.
      destruct H. destruct H.
      constructor.
      auto.
    -
      intros a b c.
      destruct a, b, c.
      intros H1 H2.
      destruct H1. destruct H.
      destruct H2. destruct H1.
      constructor.
      split.
      rewrite H; apply H1.
      rewrite H0. apply H2.
  Qed.


  Definition decode_cap (bs:list AbsByte) (tag:bool) (c:Capability_GS.t): Prop
    :=
    exists ls:list ascii,
      (* have their corrsponding bytes intialized *)
      Forall2 (fun a x => a.(value) = Some x) bs ls
      (* decode without error *)
      /\ Capability_GS.decode ls true = Some c.

  (** [True] if the list of bytes starts with given offset and offsets
      increases by one each step ending with [m] *)
  Inductive bytes_copy_offset_seq: nat -> nat -> list AbsByte -> Prop :=
  | bytes_copy_offset_seq_single:
    forall n b,
      b.(copy_offset) = Some n ->
      bytes_copy_offset_seq (S n) n [b]
  | bytes_copy_offset_seq_cons:
    forall m n b bs,
      b.(copy_offset) = Some n ->
      bytes_copy_offset_seq m (S n) bs ->
      bytes_copy_offset_seq m n (b :: bs).

  (** [True] if all bytes in given list [bl] have given provenance, and
     their offsets are sequential ending with [0] *)
  Definition split_bytes_ptr_spec (p:provenance) (bl:list AbsByte): Prop
    :=
    List.Forall (fun x => provenance_eqb p x.(prov) = true) bl
    /\ bytes_copy_offset_seq (List.length bl) 0 bl.

  Definition allocations_do_no_overlap (a1 a2:allocation) : Prop
    :=
    let a1_base := AddressValue.to_Z a1.(base) in
    let a2_base := AddressValue.to_Z a2.(base) in
    let a1_size := Z.of_nat a1.(size) in
    let a2_size := Z.of_nat a2.(size) in
    (a1_base + a1_size <= a2_base) \/ (a2_base + a2_size <= a1_base) \/ a1_size = 0 \/ a2_size = 0.


  Module Type CheriMemoryImplWithProofs
    (SW: CerbSwitchesDefs) <:
    CheriMemoryImpl(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(SW).
    Include CheriMemoryExe(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(SW).

    Import CheriMemoryTypesExe.

    Definition base_mem_invariant (m: mem_state_r) : Prop
      :=
      let cm := m.(capmeta) in
      let bm := m.(bytemap) in
      let am := m.(allocations) in

      (* All allocations are live. [allocation.(is_dead)] is only used
      for Conucopia. For others, the dead allocations are immediately
      removed.  *)
      zmap_forall (fun a => a.(is_dead) = false) am

      (* live allocatoins do not overlap *)
      /\ (forall alloc_id1 alloc_id2 a1 a2,
            alloc_id1 <> alloc_id2 ->
            ZMap.MapsTo alloc_id1 a1 am ->
            ZMap.MapsTo alloc_id2 a2 am ->
            allocations_do_no_overlap a1 a2)

      (* All keys in capmeta must be pointer-aligned addresses *)
      /\ zmap_forall_keys (fun addr => Z.modulo addr
                                     (Z.of_nat MorelloImpl.get.(alignof_pointer))
                                   = 0) cm

      (* [next_alloc_id] is sane *)
      /\
        zmap_forall_keys (fun alloc_id => alloc_id < m.(next_alloc_id)) am
      (* [last_address] is sane *)
      /\
        zmap_forall (fun a => AddressValue.to_Z a.(base) <= AddressValue.to_Z m.(last_address)) am.

    Ltac destruct_base_mem_invariant H
      :=
      let Bdead := fresh "Bdead" in
      let Bnooverlap := fresh "Bnooverlap" in
      let Balign := fresh "Balign" in
      let Bnextallocid := fresh "Bnextallocid" in
      let Blastaddr := fresh "Blastaddr" in
      destruct H as [Bdead [Bnooverlap [Balign [Bnextallocid Blastaddr]]]].

    Instance memM_MonadLaws: MonadLaws (memM_monad).
    Proof.
      split; intros;  unfold memM_monad, Monad_errS, ret, bind;
        repeat break_let.
      - f_equiv.
      -
        apply functional_extensionality.
        destruct x.
        break_let.
        destruct s; reflexivity.
      -
        apply functional_extensionality.
        destruct x.
        repeat break_let.
        repeat break_match; tuple_inversion; reflexivity.
    Qed.

    Definition lift_sum_p
      {A B:Type}
      (Pa: A -> Prop)
      (Pb: B -> Prop)
      (a:sum A B): Prop :=
      match a with
      | inl a => Pa a
      | inr b => Pb b
      end.

    Lemma init_ghost_tags_spec
      (addr: AddressValue.t)
      (size: nat)
      (capmeta: ZMap.t (bool*CapGhostState)):
      forall a tg,
        ZMap.MapsTo a tg (init_ghost_tags addr size capmeta)
        ->
          (ZMap.MapsTo a tg capmeta
           \/
             (Z.modulo a (Z.of_nat MorelloImpl.get.(alignof_pointer)) = 0
              /\
                tg = (false, {| tag_unspecified := true; bounds_unspecified := false |}))).
    Proof.
      intros a tg H.
      unfold init_ghost_tags in *.
      repeat break_let.
      apply zmap_range_init_spec in H.
      destruct H as [[H1 H2] | [[i [H3 H4]] H5]].
      -
        left.
        apply H2.
      -
        right.
        split.
        +
          subst a.
          setoid_rewrite Z.mul_comm.
          rewrite <- Z.mul_add_distr_l.
          apply ZLib.Z_mod_mult'. (* Possible TODO: use an alternative function to Z_mod_mult' so the dependency on bbv can be removed. *)
        +
          apply H5.
    Qed.

    Definition memM_same_state
      {T: Type}
      (c: memM T) : Prop
      := forall v m0 m1, c m0 = (m1, v) -> m0 = m1.

    Class SameState
      {T: Type}
      (c: memM T) : Prop
      :=
      same_state: @memM_same_state T c.

    Lemma update_mem_state_spec
      (f : mem_state -> mem_state)
      (s s' : mem_state):
      @ErrorWithState.update mem_state memMError f s = (s', inr tt) -> s' = f s.
    Proof.
      intros H.
      unfold ErrorWithState.update in H.
      unfold bind, get, put, Monad_errS, State_errS in H.
      tuple_inversion.
      reflexivity.
    Qed.

    Instance ret_SameState:
      forall {T} (x:T),  SameState (@ret memM (Monad_errS mem_state memMError) T x).
    Proof.
      intros T x v s s' H.
      Transparent ret.
      unfold ret, memM_monad, Monad_errS in H.
      Opaque ret.
      tuple_inversion.
      reflexivity.
    Qed.
    Opaque ret.

    Instance raise_SameState
      {T:Type}:
      forall x,
        SameState
          (@raise memMError (errS mem_state_r memMError)
             (Exception_errS mem_state_r memMError) T
             x).
    Proof.
      intros e x s s' H.
      invc H.
      reflexivity.
    Qed.
    Opaque raise.

    Instance bind_SameState
      {T T': Type}
      {M: memM T'}
      {C: T' -> memM T}
      :
      (SameState M) ->  (forall x, SameState (C x)) -> SameState (bind M C).
    Proof.
      intros MS CS.
      intros x s s' H.
      unfold bind, Monad_errS in H.
      break_let.
      break_match_hyp;[tuple_inversion|].
      -
        specialize (MS _ _ _  Heqp).
        assumption.
      -
        specialize (MS _ _ _  Heqp).
        subst.
        specialize (CS t x m s').
        apply CS.
        apply H.
    Qed.

    Instance get_SameState
      :SameState get.
    Proof.
      intros s s' st.
      intros H.
      unfold get, State_errS in *.
      tuple_inversion.
      reflexivity.
    Qed.

    Instance fail_SameState {T:Type}:
      forall l e,
        SameState (@fail T l e).
    Proof.
      intros l e.
      unfold fail.
      break_match;
        apply raise_SameState.
    Qed.

    Instance fail_noloc_SameState {T:Type}:
      forall e,
        SameState (@fail_noloc T e).
    Proof.
      intros e.
      unfold fail_noloc.
      apply fail_SameState.
    Qed.

    Instance serr2InternalErr_SameState
      {T: Type}
      {e: serr T}:
      SameState (serr2InternalErr e).
    Proof.
      unfold serr2InternalErr.
      destruct e.
      apply raise_SameState.
      apply ret_SameState.
    Qed.

    Instance liftM_SameState
      {A T : Type}
      {a : memM A}:

      SameState a ->

      forall x : A -> T,
        SameState
          (@liftM memM (Monad_errS mem_state memMError) A T x a).
    Proof.
      intros s H x.
      unfold liftM.
      apply bind_SameState.
      assumption.
      intros x0.
      apply ret_SameState.
    Qed.

    Instance option2memM_SameState
      {A:Type}
      (s:string)
      (v: option A):
      SameState (option2memM s v).
    Proof.
      unfold option2memM.
      break_match_goal;
      typeclasses eauto.
    Qed.

    Instance sequence_same_state
      {A: Type}:
      forall (ls: list (memM A)),
        (List.Forall (SameState) ls) ->
        SameState (sequence ls).
    Proof.
      Transparent ret bind.
      intros ls H.
      intros ll s s' S.
      revert ll H S.
      induction ls; intros.
      -
        cbn in S.
        unfold ret, Monad_errS in S.
        tuple_inversion.
        reflexivity.
      -
        destruct ll.
        +
          cbv in S.
          cbn.
          unfold liftM, ret, bind in *.
          repeat break_match_hyp;repeat break_let;repeat tuple_inversion.
          *
            invc H.
            apply H2 in Heqp0.
            assumption.
          *
            inversion H.
            subst.
            apply H2 in Heqp1.
            subst.
            eapply IHls;eauto.
        +
          pose proof (sequence_len_errS _ _ _ _ S).
          destruct l;[inv H0|].
          invc S.
          eapply (IHls (inr l)).
          *
            invc H.
            auto.
          *
            invc H.
            repeat break_let.
            repeat break_match_hyp;repeat break_let;repeat tuple_inversion.
            apply H4 in Heqp1.
            subst m.
            clear H4 a H0.
            cbn.
            rewrite Heqp0.
            invc H3.
            reflexivity.
            Opaque ret bind.
    Qed.

    Instance zmap_sequence_SameState
      {A: Type}
      (mv: ZMap.t (memM A)):
      zmap_forall SameState mv ->
      SameState (zmap_sequence mv).
    Proof.
      intros H.
      unfold zmap_sequence.
      break_let.
      pose proof (sequence_same_state l0) as SS.
      autospecialize SS.
      eapply zmap_forall_Forall_elements;eauto.
      clear H.
      apply bind_SameState.
      assumption.
      intros x.
      apply ret_SameState.
    Qed.


    Instance zmap_mmapi_SameState
      {A B: Type}
      (c: ZMap.key -> A -> memM B)
      (zm : ZMap.t A):

      (forall k v, SameState (c k v)) ->
      SameState (zmap_mmapi c zm).
    Proof.
      intros C zm' m0 m1 H.
      unfold zmap_mmapi in H.
      apply zmap_sequence_SameState in H;[assumption|].
      clear H.

      unfold zmap_forall.
      intros k v H.
      apply mapi_inv in H.
      destruct H as [a [k' [H1 [H2 H3]]]].
      subst.
      apply C.
    Qed.

    Lemma sequence_spec_same_state_memM
      {A:Type}
      (s : mem_state)
      (old : list (memM A))
      (new : list A):
      List.Forall memM_same_state old ->
      sequence old s = (s, inr new) ->
      Forall2 (fun m r => m s = (s, inr r)) old new.
    Proof.
      Transparent ret bind liftM.
      intros C H.
      unfold sequence, mapT, Traversable_list, mapT_list in H.
      unfold Applicative_Monad, Applicative.pure, Monad_errS, ret,
        Applicative.ap, apM, bind, liftM, ret in H.
      cbn in H.
      generalize dependent new.
      dependent induction old;intros.
      -
        tuple_inversion.
        constructor.
      -
        repeat break_let.
        repeat break_match; repeat tuple_inversion.
        cbn.
        invc C.
        assert(m = s).
        {
          apply H1 in Heqp1.
          subst.
          reflexivity.
        }
        subst m.
        constructor.
        +
          assumption.
        +
          apply IHold; assumption.
          Opaque ret bind liftM.
    Qed.

    Instance find_live_allocation_SameState
      (addr : AddressValue.t):
      SameState (find_live_allocation addr).
    Proof.
      intros res s s' H.
      unfold find_live_allocation in H.
      Transparent ret bind get.
      unfold bind, get, ret, memM_monad, Monad_errS, State_errS in H.
      tuple_inversion.
      reflexivity.
      Opaque ret bind get.
    Qed.

    Instance get_allocation_opt_SameState
      (alloc_id : Z):
      SameState (get_allocation_opt alloc_id).
    Proof.
      intros res s s' H.
      Transparent ret bind get.
      unfold get_allocation_opt, bind, get, ret, memM_monad, Monad_errS, State_errS in H.
      tuple_inversion.
      reflexivity.
      Opaque ret bind get.
    Qed.

    Instance mapT_list_SameState
      {A B:Type}
      {l : list A}
      {f: A -> memM B}:
      Forall (fun x  => SameState (f x)) l ->
      SameState (mapT_list f l).
    Proof.
      intros H.
      induction l.
      -
        cbn.
        apply ret_SameState.
      -
        cbn.
        unfold apM.
        repeat apply bind_SameState.
        apply ret_SameState.
        intros x.
        apply liftM_SameState.
        +
          apply Forall_inv in H.
          assumption.
        +
          intros.
          apply liftM_SameState.
          apply IHl.
          apply Forall_inv_tail in H.
          assumption.
    Qed.

    Opaque bind raise ret get fail fail_noloc serr2InternalErr.
    Ltac same_state_step
      :=
      match goal with
      |[|- SameState (bind _ _)] => apply bind_SameState
      |[|- SameState (raise _)] => apply raise_SameState
      |[|- SameState (ret _)] => apply ret_SameState
      |[|- SameState get] => apply get_SameState
      |[|- SameState (fail _ _)] => apply fail_SameState
      |[|- SameState (fail_noloc _)] => apply fail_noloc_SameState
      |[|- SameState (serr2InternalErr _)] => apply serr2InternalErr_SameState
      |[|- SameState (liftM _ _)] => apply liftM_SameState
      |[|- SameState (mapT_list _ _)] => apply mapT_list_SameState
      |[|- SameState (option2memM _ _)] => apply option2memM_SameState
      |[|- SameState _] => typeclasses eauto
      end ; intros.

    Ltac same_state_steps :=
      repeat (match goal with
              | |- SameState (match _ with _ => _ end) => break_match_goal
              | |- SameState _ => same_state_step
              | |- context [match _ with _ => _ end] => break_match_goal
              | |- context [if _ then _ else _] => break_match_goal
              end).

    Lemma find_live_allocation_res_consistent
      (addr : AddressValue.t)
      (alloc : allocation)
      (alloc_id : Z)
      (s s' : mem_state):
      find_live_allocation addr s = (s', inr (Some (alloc_id, alloc))) ->
      ZMap.MapsTo alloc_id alloc s'.(allocations).
    Proof.
      intros H.
      unfold find_live_allocation in H.
      Transparent ret bind get.
      unfold bind, get, ret, memM_monad, Monad_errS, State_errS in H.
      Opaque ret bind get.
      tuple_inversion.
      revert H2.
      match goal with
      | [ |- context[ZMap.fold ?f _ _]] =>
          remember f as ff
      end.
      revert alloc_id alloc.
      cut(
          (fun res =>
             match res with
             | None => True
             | Some (alloc_id, alloc) => ZMap.MapsTo alloc_id alloc (allocations s')
             end) (ZMap.fold ff (allocations s') None)).
      {
        clear.
        intros H alloc_id alloc H2.
        cbn in H.
        break_match_hyp.
        -
          break_let.
          invc H2.
          assumption.
        -
          inv H2.
      }
      apply fold_rec_nodep.
      -
        trivial.
      -
        intros k e a H H0.
        break_match_goal;[|trivial].
        break_match_hyp;break_let;subst.
        +
          invc Heqo.
          assumption.
        +
          break_match.
          *
            invc Heqo.
            assumption.
          *
            inv Heqo.
    Qed.

    Lemma fetch_bytes_len
      (addr : ZMap.key)
      (bm : ZMap.t AbsByte)
      (sz: nat):
      Datatypes.length (fetch_bytes bm addr sz) = sz.
    Proof.
      unfold fetch_bytes.
      rewrite map_length.
      rewrite list_init_len.
      reflexivity.
    Qed.

    Lemma split_bytes_success
      (bs : list AbsByte)
      (p : provenance)
      :
      split_bytes_ptr_spec p bs ->
      (exists (tag : bool) (cs: list (option ascii)) (p' : provenance),
          (* provenance_eqb p p' = true /\ *)
          split_bytes bs = inr (p', tag, cs)).
    Proof.
      intros H.
      destruct H as [HP HO].
      Transparent bind get put ret raise.
      unfold split_bytes, Monad_either, bind, get, put, ret, Monad_errS, State_errS, Exception_either, raise.
      Opaque bind get put ret raise.
      repeat break_let.
      destruct bs.
      -
        cbn in HO.
        inversion HO.
      -
        remember (split_bytes_aux (a :: bs) (prov a)) as s eqn:S.
        destruct s as [[prov_maybe rev_values] offset_status_maybe].
        symmetry in S.
        remember (rev rev_values) as cs eqn:CS.
        remember (CapFns.is_some offset_status_maybe && CapFns.is_some prov_maybe) as tag.
        remember (Values.opt_def (PNVI_prov Prov_none) prov_maybe) as p'.
        exists tag, cs, p'.
        reflexivity.
    Qed.

    Lemma split_bytes_aux_length
      (o : option nat)
      (p : option provenance)
      (l : list (option ascii))
      (bs : list AbsByte)
      (p0 : provenance):
      split_bytes_aux bs p0 = (p, l, o) -> Datatypes.length bs = Datatypes.length l.
    Proof.
      unfold split_bytes_aux.
      (* Some generalizations before induction *)
      remember (@nil (option ascii)) as l0.
      setoid_replace (@Datatypes.length AbsByte bs) with ((@Datatypes.length AbsByte bs)  + (@Datatypes.length (option ascii) l0))%nat.
      2:{
        subst.
        cbn.
        lia.
      }
      clear Heql0.
      generalize (Some p0) as op0. clear p0.
      generalize (Some O) as oo0.
      revert l p o l0.
      (* proof by induction *)
      induction bs; intros.
      -
        cbn in H.
        tuple_inversion.
        reflexivity.
      -
        apply IHbs in H.
        cbn in H.
        cbn.
        lia.
    Qed.

    Lemma split_bytes_length
      (tag : bool)
      (cs : list (option ascii))
      (bs : list AbsByte)
      (p: provenance):
      split_bytes bs = inr (p, tag, cs) ->
      length bs = length cs.
    Proof.
      destruct bs; intros H;[inv H|].
      rename a into b.
      cbn -[split_bytes_aux] in H.
      Transparent bind get put ret.
      unfold Monad_either, bind, get, put, ret, Monad_errS, State_errS in H.
      Opaque bind get put ret.
      repeat break_let.
      repeat break_match_hyp; try inl_inr; try repeat inl_inr_inv; subst; try bool_inv; rewrite rev_length.
      rename o0 into p, bs into bs'.
      remember (b::bs') as bs.
      remember (prov b) as p0.
      clear Heqbs Heqp1 b bs'.
      rename Heqp0 into H.
      (* Done with monadic stuff *)
      apply (split_bytes_aux_length _ _ _ _ _ H).
    Qed.

    Lemma split_bytes_aux_values
      (o : option nat)
      (p : option provenance)
      (l : list (option ascii))
      (bs : list AbsByte)
      (p0 : provenance):
      split_bytes_aux bs p0 = (p, l, o) ->
      Forall2 (fun (a : AbsByte) (ov : option ascii) => ov = value a) bs (rev l).
    Proof.
      Local Open Scope nat.
      intros SS.

      pose proof (split_bytes_aux_length _ _ _ _ _ SS) as LBS.
      unfold split_bytes_aux in SS.
      remember (@nil (option ascii)) as l'.
      assert(length l = length bs + length l') as LL.
      {
        subst l'.
        cbn.
        lia.
      }

      clear Heql'.
      revert SS.
      generalize (Some p0) as op0. clear p0.
      generalize (Some O) as oo0.
      intros oo0 op0 SS.

      cut(Forall2 (fun (a : AbsByte) (ov : option ascii) => ov = value a) bs (rev (firstn (length bs) l)) /\
            l' = skipn (length bs) l
         ).
      {
        clear SS.
        intros [H1 _].
        rewrite LBS in H1.
        rewrite firstn_all in H1.
        assumption.
      }
      clear LBS.

      (* done with generalization *)

      revert l op0 p oo0 o l' LL SS.
      induction bs; intros.
      -
        split; cbn.
        +
          rewrite firstn_O.
          cbn.
          constructor.
        +
          rewrite skipn_O.
          cbn in SS.
          tuple_inversion.
          auto.
      -
        cbn in SS.
        apply IHbs in SS; clear IHbs.
        2:{
          clear - LL.
          cbn in LL.
          cbn.
          lia.
        }
        destruct SS as [SS1 SS2].
        split.
        +
          clear p op0 o oo0.
          cbn. cbn in *.

          assert(rev (firstn (S (Datatypes.length bs)) l) =
                   value a :: (rev (firstn (Datatypes.length bs) l))) as LP.
          {
            rewrite <- rev_unit.
            f_equiv.
            rewrite <- list.take_S_r.
            reflexivity.
            clear - SS2.
            generalize dependent (Datatypes.length bs).
            intros n H.
            symmetry in H.
            rewrite MachineWord.MachineWord.nth_error_lookup.
            eapply skipn_cons_nth_error;eauto.
          }
          rewrite LP.
          constructor;[reflexivity|assumption].
        +
          clear - SS2 LL.
          cbn in LL.
          cbn.
          generalize dependent (length bs).
          intros n LL SS2. clear bs.
          destruct l.
          *
            rewrite list.drop_nil in SS2.
            inversion SS2.
          *
            cbn.
            cbn in LL.
            invc LL.
            revert l l' a o a H0 SS2.
            induction n; intros.
            --
              rewrite skipn_O.
              rewrite skipn_O in SS2.
              inversion SS2.
              auto.
            --
              rewrite skipn_cons in SS2.
              destruct l.
              ++
                rewrite list.drop_nil in SS2.
                inversion SS2.
              ++
                rewrite skipn_cons.
                eapply IHn; eauto.

                Local Close Scope nat.
    Qed.

    Lemma split_bytes_values
      (tag : bool)
      (cs : list (option ascii))
      (bs : list AbsByte)
      (p:provenance):
      split_bytes bs = inr (p, tag, cs) ->
      Forall2 (fun a ov => ov = value a) bs cs.
    Proof.
      destruct bs; intros H;[inv H|].
      rename a into b.
      cbn -[split_bytes_aux] in H.
      Transparent bind get put ret.
      unfold Monad_either, bind, get, put, ret, Monad_errS, State_errS in H.
      Opaque bind get put ret.
      repeat break_let.
      inl_inr_inv.
      rewrite H3.
      (* Done with monadic stuff *)

      (* Some generalizations before induction *)
      clear - Heqp0 H3.
      rename o0 into p, bs into bs'.
      remember (b::bs') as bs.
      remember (prov b) as p0.
      clear Heqbs Heqp1 b bs'.
      rename Heqp0 into H, H3 into R.
      subst cs.

      (* apply generalized sub-lemma *)
      apply split_bytes_aux_values in H.
      apply H.
    Qed.

    Lemma extract_unspec_spec
      (cs : list (option ascii))
      (ls : list ascii):
      Forall2 (fun ov v => ov = Some v) cs ls ->
      extract_unspec cs = Some ls.
    Proof.
      intros H.
      unfold extract_unspec.
      rewrite <- fold_left_rev_right.
      rewrite rev_involutive.
      induction H.
      -
        cbn.
        reflexivity.
      -
        rewrite list.foldr_cons.
        rewrite IHForall2. clear IHForall2.
        destruct x.
        invc H.
        reflexivity.
        inversion H.
    Qed.

    Lemma fetch_and_decode_cap_success
      (addr: ZMap.key)
      (c: Capability_GS.t)
      (bm: ZMap.t AbsByte):
      split_bytes_ptr_spec Prov_disabled (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)) ->
      decode_cap (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)) true c ->
      fetch_and_decode_cap bm addr true = inr c.
    Proof.
      intros S D.
      remember (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)) as bs.
      apply split_bytes_success in S.

      destruct S as [tag [cs [p' S]]].
      unfold decode_cap in D.
      unfold fetch_and_decode_cap.
      Transparent ret bind get.
      unfold memM_monad, Monad_errS, State_errS, Monad_either, ret, bind.
      generalize dependent (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)).
      intros bs' E.
      subst bs'.
      break_match.
      -
        inl_inr.
      -
        repeat break_let.
        subst.
        inl_inr_inv.
        subst.
        destruct D as [ls [BL D]].
        (* [bs] [cs] and [ls] relation is a bit tricky here, but workable *)

        apply split_bytes_values in Heqs.
        rename Heqs into BC.

        assert(Forall2 (fun ov v => ov = Some v ) cs ls) as CL.
        {
          clear - BC BL.
          apply Forall2_flip in BC.
          eapply list.Forall2_transitive;eauto.
          clear.
          intros x y z H H0.
          cbn in *.
          subst.
          assumption.
        }

        apply extract_unspec_spec in CL.
        rewrite CL.
        cbn.
        rewrite D.
        reflexivity.
        Opaque ret bind get.
    Qed.

    Lemma cap_bounds_within_alloc_true:
      forall a c,
        cap_bounds_within_alloc_bool c a = true -> cap_bounds_within_alloc c a.
    Proof.
      intros a c H.
      unfold cap_bounds_within_alloc.
      unfold cap_bounds_within_alloc_bool in H.
      lia.
    Qed.

    Lemma cap_bounds_within_alloc_false:
      forall a c,
        cap_bounds_within_alloc_bool c a = false -> ~ cap_bounds_within_alloc c a.
    Proof.
      intros a c H.
      unfold cap_bounds_within_alloc.
      unfold cap_bounds_within_alloc_bool in H.
      lia.
    Qed.

    Fact update_state_capmeta:
      forall s s' c,
        @ErrorWithState.update mem_state memMError (mem_state_with_capmeta c) s = (s', inr tt)
        -> s'.(capmeta) = c /\ s'.(bytemap) = s.(bytemap).
    Proof.
      intros s s' c H.
      Transparent ret bind get put ErrorWithState.update.
      unfold ErrorWithState.update, memM_monad, Monad_errS, State_errS, ret, bind, get, put, mem_state_with_capmeta in H.
      Opaque ret bind get put ErrorWithState.update.
      split;destruct s';inversion H;reflexivity.
    Qed.

    Lemma fail_inr_inv
      {A:Type}
      {loc : location_ocaml}
      {m : MemCommonExe.mem_error}
      {s s' : mem_state}
      {v : A}:
      @fail A loc m s   = (s', inr v) -> False.
    Proof.
      intros H.
      Transparent fail raise.
      unfold fail, raise, Exception_errS in H.
      Opaque fail raise.
      break_match_hyp;discriminate.
    Qed.

    Lemma raise_inr_inv
      {A E:Type}
      {e: E}
      {s s' : mem_state}
      {v : A}:

      @raise E (errS mem_state_r E) (Exception_errS mem_state_r E) A e s
      = (s', inr v) -> False.
    Proof.
      intros H.
      Transparent raise.
      unfold raise, Exception_errS in H.
      tuple_inversion.
    Qed.

    Lemma get_inv
      {s : mem_state}:
      @get mem_state_r memM (State_errS mem_state memMError) s = (s, @inr memMError mem_state_r s).
    Proof.
      Transparent get.
      unfold get, State_errS.
      Opaque get.
      reflexivity.
    Qed.

    Lemma bind_memM_inv
      {T T': Type}
      {m: memM T'}
      {c: T' -> memM T}
      {x: T}
      {s s': mem_state}
      :
      (bind m c) s = (s', inr x) ->
      exists s'' y, m s = (s'', inr y) /\ c y s'' = (s', inr x).
    Proof.
      Transparent bind ret.
      unfold bind, ret, memM_monad, Monad_errS, Monad_either.
      Opaque bind ret.
      repeat break_let.
      intros H.
      break_match.
      tuple_inversion.
      subst.
      eauto.
    Qed.

    Lemma bind_memM_inv_same_state
      {T T': Type}
      {m: memM T'}
      `{MS: SameState _ m}
      {c: T' -> memM T}
      {x: T}
      {s s': mem_state}
      :
      (bind m c) s = (s', inr x) ->
      exists y, m s = (s, inr y) /\ c y s = (s', inr x).
    Proof.
      Transparent bind ret.
      unfold bind, ret, memM_monad, Monad_errS, Monad_either.
      Opaque bind ret.
      repeat break_let.
      intros H.
      specialize (MS _ _ _ Heqp).
      break_match.
      tuple_inversion.
      subst.
      eauto.
    Qed.

    Lemma bind_serr_inv
      {T T': Type}
      {m: serr T}
      {c: T -> serr T'}
      {x: T'}
      :
      (@bind (sum string) (Monad_either string) T T' m c) = inr x ->
      exists y, m = inr y /\ c y = inr x.
    Proof.
      Transparent bind ret.
      unfold bind, ret, memM_monad, Monad_errS, Monad_either.
      Opaque bind ret.
      repeat break_let.
      intros H.
      break_match.
      discriminate.
      subst.
      exists t.
      auto.
    Qed.

    Lemma sassert_inv
      {b : bool}
      {s : string}
      {u : unit}:
      sassert b s = inr u -> b = true.
    Proof.
      unfold sassert.
      Transparent ret raise.
      unfold ret, raise, Monad_either, Exception_serr.
      Opaque ret raise.
      intros H.
      break_match_hyp;[reflexivity|discriminate].
    Qed.

    Lemma ret_memM_inv
      {A:Type}
      {v:A}
      {s: mem_state}:
      @ret memM memM_monad A v s = (s, @inr memMError A v).
    Proof.
      Transparent ret.
      unfold ret, memM_monad, Monad_errS, Monad_either.
      Opaque ret.
      reflexivity.
    Qed.

    Lemma ret_serr_inv
      {A:Type}
      {x:A}:
      @ret serr (Monad_either string) A x = @inr string A x.
    Proof.
      Transparent ret.
      unfold ret, memM_monad, Monad_errS, Monad_either.
      Opaque ret.
      reflexivity.
    Qed.

    Lemma serr2InternalErr_inv
      {A:Type}
      {x:A}
      m
      {s: mem_state}:
      serr2InternalErr m s = (s, inr x) -> m = inr x.
    Proof.
      intros H.
      Transparent serr2InternalErr ret.
      unfold serr2InternalErr, ret, memM_monad, Monad_errS, Monad_either in H.
      Opaque serr2InternalErr ret.
      destruct m.
      apply raise_inr_inv in H. tauto.
      tuple_inversion.
      reflexivity.
    Qed.

    Ltac htrim :=
      repeat break_match_hyp; repeat break_let; try subst; try tuple_inversion; cbn in *.

    Ltac state_inv_step :=
      repeat match goal with
        (* memM bind with var name *)
        |[ H: (bind _ (fun x => _)) ?s = (_ ,inr _) |- _ ] =>
           tryif (apply bind_memM_inv_same_state in H)
           then
             ((* idtac H "bind (memM, same state)" x; *)
              let H1 := fresh H in
              let H2 := fresh H in
              let x' := fresh x in
              destruct H as [x' [H1 H2]]
              ; htrim)
           else
             ((*idtac H "bind (memM)" x; *)
              let H1 := fresh H in
              let H2 := fresh H in
              let x' := fresh x in
              let s' := fresh s in
              apply bind_memM_inv in H;
              destruct H as [s' [x [H1 H2]]]
              ; htrim)
        (* anonymous memM bind *)
        |[ H: (bind _ (fun _ => _)) ?s = (_ ,inr _) |- _ ] =>
           tryif (apply bind_memM_inv_same_state in H)
           then
             ((*idtac H "bind (memM, same_state, anon)"; *)
              let H1 := fresh H in
              let H2 := fresh H in
              let u := fresh "u" in
              destruct H as [u [H1 H2]]
              ; htrim)
           else
             ((*idtac H "bind (memM, anon)"; *)
              let H1 := fresh H in
              let H2 := fresh H in
              let u := fresh "u" in
              let s' := fresh s in
              apply bind_memM_inv in H;
              destruct H as [s' [u [H1 H2]]]
              ; htrim)
        (* serr bind with var name *)
        | [ H: bind _ (fun x => _) = inr _ |- _]
          =>
            (* idtac H "bind (serr)" x; *)
            apply bind_serr_inv in H;
            let H1 := fresh H in
            let H2 := fresh H in
            let x' := fresh x in
            destruct H as [x' [H1 H2]]
            ; htrim
        (* anonymous serr bind *)
        | [ H: bind _ (fun _ => _) = inr _ |- _]
          =>
            (* idtac H "bind (serr, anon)"; *)
            apply bind_serr_inv in H;
            let H1 := fresh H in
            let H2 := fresh H in
            let u := fresh "u" in
            destruct H as [u [H1 H2]]
            ; htrim
        | [H: fail _ _ ?s = (?s, inr _) |- _] =>
            (* idtac H "fail"; *)
            apply fail_inr_inv in H; tauto
            ; htrim
        | [H: serr2InternalErr _ ?s = (?s, inr _) |- _] =>
            (* idtac H "serr2InternalErr"; *)
            apply serr2InternalErr_inv in H
            ; htrim
        | [H: ret _ _ = (_, inr _) |- _] =>
            (* idtac H "ret (memM)"; *)
            rewrite ret_memM_inv in H
            ; htrim
        | [H: @ret serr (Monad_either string) _ ?x = inr _ |- _] =>
            (* idtac H "ret (serr)"; *)
            rewrite ret_serr_inv in H
            ; htrim
        | [H: get _ = (_, inr _) |- _] =>
            (* idtac H "get"; *)
            rewrite get_inv in H
            ; htrim
        | [H: sassert _ _ = inr _ |- _] =>
            (* idtac H "sassert"; *)
            apply sassert_inv in H
            ; htrim
        | [H: inl _ = inl _ |- _] => inversion H; clear H; htrim
        | [H: inr _ = inr _ |- _] => inversion H; clear H; htrim
        end.

    Section MemMwithInvariant.
      Variable invr: mem_state_r -> Prop.

      Definition post_exec_invariant
        {T: Type} (mem_state: mem_state_r) (M: memM T) : Prop
        :=
        lift_sum_p
          (fun _ => True)
          invr
          (execErrS M mem_state).

      Class PreservesInvariant
        {T: Type} (s: mem_state_r) (M: memM T) : Prop
        :=
        preserves_invariant:
          invr s -> post_exec_invariant s M.


      (* [SameState] is stronger and implies [PreservesInvariant] *)
      #[global] Instance SameStatePreserves
        {T: Type}
        (M: memM T)
        `{H: SameState T M}:
        forall s, PreservesInvariant s M.
      Proof.
        intros s.
        unfold SameState, memM_same_state in H.
        unfold PreservesInvariant, post_exec_invariant, lift_sum_p.
        break_match.
        trivial.
        unfold execErrS in Heqs0.
        break_let.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        specialize (H (inr t) s m Heqp).
        subst.
        trivial.
      Qed.

      Instance ret_PreservesInvariant:
        forall s {T} (x:T), PreservesInvariant s (ret x).
      Proof.
        typeclasses eauto.
      Qed.
      Opaque ret.

      Instance raise_PreservesInvariant
        {T:Type}:
        forall s x,
          PreservesInvariant s
            (@raise memMError (errS mem_state_r memMError)
               (Exception_errS mem_state_r memMError) T
               x).
      Proof.
        typeclasses eauto.
      Qed.
      Opaque raise.

      (* Most general form, no connection between [s] and [s'] and nothing is known about [x] *)
      Instance bind_PreservesInvariant_same_state
        {T T': Type}
        {M: memM T'}
        {C: T' -> memM T}
        {MS: SameState M}
        :
        forall s,
          (forall x, PreservesInvariant s (C x))
          -> PreservesInvariant s (bind M C).
      Proof.
        Transparent bind.
        intros s MC H0.
        unfold PreservesInvariant, post_exec_invariant, execErrS, evalErrS, lift_sum_p in *.
        repeat break_let.
        cbn in *.
        repeat break_let.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        break_match_hyp.
        tuple_inversion.
        subst.

        specialize (MS (inr t0) s m0 Heqp0).
        subst m0.

        specialize (MC t0 H0).
        unfold execErrS, evalErrS, lift_sum_p in MC.
        break_let.
        tuple_inversion.
        apply MC.
        Opaque bind.
      Qed.

      (* Most general form, no connection between [s] and [s'] and nothing is known about [x] *)
      Instance bind_PreservesInvariant
        {T T': Type}
        {M: memM T'}
        {C: T' -> memM T}
        :
        forall s,
          PreservesInvariant s M ->
          (forall s' x, PreservesInvariant s' (C x))
          -> PreservesInvariant s (bind M C).
      Proof.
        Transparent bind.
        intros s MH MC H0.
        unfold PreservesInvariant, post_exec_invariant, execErrS, evalErrS, lift_sum_p in *.
        repeat break_let.
        cbn in *.
        repeat break_let.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        break_match_hyp.
        tuple_inversion.
        subst.

        specialize (MH H0).
        tuple_inversion.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        specialize (MC _ t0 MH).
        unfold execErrS, evalErrS, lift_sum_p in MC.
        break_let.
        tuple_inversion.
        apply MC.
        Opaque bind.
      Qed.

      (* More specific, allows reasoning about the value of [x] *)
      Instance bind_PreservesInvariant_value
        {T T': Type}
        {m: memM T'}
        {c: T' -> memM T}
        :
        forall s,
          (invr s -> (forall s' x, m s = (s', inr x) -> (invr s' /\ PreservesInvariant s' (c x))))
          -> PreservesInvariant s (bind m c).
      Proof.
        Transparent ret raise bind.
        intros s MH H0.
        specialize (MH H0).
        unfold PreservesInvariant, post_exec_invariant, execErrS, evalErrS, lift_sum_p.
        repeat break_let.
        cbn in *.

        break_let.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        break_match_hyp.
        tuple_inversion.
        subst.
        specialize (MH m1 t0).
        destruct MH as [MI MH].
        - reflexivity.
        -
          clear - MH Heqp MI.
          unfold PreservesInvariant, post_exec_invariant in MH.
          specialize (MH MI).
          unfold execErrS, evalErrS, lift_sum_p, raise, ret, Exception_either, Monad_either  in MH.
          break_let.
          repeat break_match; try break_let;
            try inl_inr_inv; subst.

          repeat tuple_inversion.
          repeat tuple_inversion.
          inl_inr.
          inl_inr.
          tuple_inversion.
          assumption.
          Opaque ret raise bind.
      Qed.

      (* More generic, allows reasoning about the value of [x] assume state does not change *)
      Instance bind_PreservesInvariant_value_SameState
        {T T': Type}
        {m: memM T'}
        {c: T' -> memM T}
        {MS: SameState m}
        :
        forall s,
          (invr s -> (forall x, m s = (s, inr x) -> PreservesInvariant s (c x)))
          -> PreservesInvariant s (bind m c).
      Proof.
        intros s H.
        apply bind_PreservesInvariant_value.
        intros H0 s' x H1.
        assert(s = s').
        {
          eapply MS.
          eauto.
        }
        subst s'.
        split.
        auto.
        apply H; auto.
      Qed.

      (* More specific, allows reasoning about the value of [x].
         Does not require [M] preserve invariant.
       *)
      Instance bind_PreservesInvariant_full
        {T T': Type}
        {m: memM T'}
        {c: T' -> memM T}
        :
        forall s,
          (invr s ->
           (forall s' x, m s = (s', inr x) -> post_exec_invariant s' (c x)))
          -> PreservesInvariant s (bind m c).
      Proof.
        Transparent ret raise bind.
        intros s MH.
        unfold PreservesInvariant, post_exec_invariant.
        intros H0.
        specialize (MH H0).
        unfold execErrS, evalErrS, lift_sum_p.
        repeat break_let.
        cbn in *.
        break_let.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        break_match_hyp.
        tuple_inversion.
        subst.
        specialize (MH m1 t0).
        autospecialize MH.
        reflexivity.
        unfold post_exec_invariant in MH.

        unfold execErrS, evalErrS, lift_sum_p, raise, ret, Exception_either, Monad_either  in MH.
        break_let.
        repeat break_match; try break_let;
          try inl_inr_inv; subst.

        repeat tuple_inversion.
        repeat tuple_inversion.
        inl_inr.
        inl_inr.
        tuple_inversion.
        assumption.
        Opaque ret raise bind.
      Qed.

      (* More specific, allows reasoning about the value of [x].
         Requires [M] preserve invariant.
       *)
      Instance bind_PreservesInvariant_full_with_intermediate_state
        {T T': Type}
        {m: memM T'}
        {c: T' -> memM T}
        :
        forall s,
          (invr s ->
           (forall s' x, m s = (s', inr x) -> (invr s' /\ post_exec_invariant s' (c x))))
          -> PreservesInvariant s (bind m c).
      Proof.
        Transparent ret raise bind.
        intros s MH.
        unfold PreservesInvariant, post_exec_invariant.
        intros H0.
        specialize (MH H0).
        unfold execErrS, evalErrS, lift_sum_p.
        repeat break_let.
        cbn in *.
        break_let.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        break_match_hyp.
        tuple_inversion.
        subst.
        specialize (MH m1 t0).
        destruct MH as [MI MH].
        - reflexivity.
        -
          clear - MH Heqp MI.
          unfold post_exec_invariant in MH.

          unfold execErrS, evalErrS, lift_sum_p, raise, ret, Exception_either, Monad_either  in MH.
          break_let.
          repeat break_match; try break_let;
            try inl_inr_inv; subst.

          repeat tuple_inversion.
          repeat tuple_inversion.
          inl_inr.
          inl_inr.
          tuple_inversion.
          assumption.
          Opaque ret raise bind.
      Qed.

      (* Special case of bind, where the state is passed to the continuation *)
      Instance bind_get_PreservesInvariant
        {T: Type}
        {C: mem_state_r -> memM T}
        :
        forall s,
          PreservesInvariant s (C s)
          -> PreservesInvariant s (bind get C).
      Proof.
        Transparent bind ret raise get.
        intros s MH MI.
        unfold post_exec_invariant.
        cbn.
        unfold execErrS, evalErrS, lift_sum_p in *.
        break_let.
        cbn.
        break_match;auto.
        break_match_hyp.
        inl_inr.
        inl_inr_inv.
        subst.
        specialize (MH MI).
        unfold post_exec_invariant in MH.
        unfold execErrS, evalErrS, lift_sum_p in MH.
        break_let.
        tuple_inversion.
        cbn in MH.
        auto.
        Opaque bind ret raise get.
      Qed.

      (** generic version, where [m] does not depend on [s] *)
      Instance put_PreservesInvariant:
        forall s m, invr m -> PreservesInvariant s (put m).
      Proof.
        intros s m H H0.
        apply H.
      Qed.

      (** dependent version, where [m] depends on [s] *)
      Instance put_PreservesInvariant':
        forall s m, (invr s -> invr m) -> PreservesInvariant s (put m).
      Proof.
        intros s m D H0.
        apply D.
        apply H0.
      Qed.

      Instance get_PreservesInvariant:
        forall s, PreservesInvariant s get.
      Proof.
        typeclasses eauto.
      Qed.

      Instance update_PreservesInvariant
        {f: mem_state_r -> mem_state_r}
        :
        forall s,
          (forall m, invr m ->  invr (f m)) ->
          PreservesInvariant s (ErrorWithState.update f).
      Proof.
        intros s H MI.
        apply H, MI.
      Qed.

      Instance liftM_PreservesInvariant
        {A T : Type}
        {a : memM A}:

        forall s,
          PreservesInvariant s a ->

          forall x : A -> T,
            PreservesInvariant s
              (@liftM memM (Monad_errS mem_state memMError) A T x a).
      Proof.
        Transparent liftM.
        intros s H x.
        unfold liftM.
        apply bind_PreservesInvariant.
        assumption.
        intros x0.
        apply ret_PreservesInvariant.
        Opaque liftM.
      Qed.

      Instance fail_PreservesInvariant {T:Type}:
        forall s l e,
          PreservesInvariant s (@fail T l e).
      Proof.
        intros s l e.
        typeclasses eauto.
      Qed.

      Instance fail_noloc_PreservesInvariant {T:Type}:
        forall s e,
          PreservesInvariant s (@fail_noloc T e).
      Proof.
        typeclasses eauto.
      Qed.

      Instance serr2InternalErr_PreservesInvariant
        {T: Type}
        {e: serr T}:
        forall s,
          PreservesInvariant s (serr2InternalErr e).
      Proof.
        typeclasses eauto.
      Qed.

      Instance sequence_PreservesInvariant
        {A:Type}:
        forall s,
        forall (ls: list (memM A)),
          Forall (fun e => (forall s':mem_state_r, PreservesInvariant s' e)) ls ->
          PreservesInvariant s (sequence ls).
      Proof.
        intros s ls H.
        revert s.
        unfold sequence.
        induction ls; intros s; cbn.
        -
          apply ret_PreservesInvariant.
        -
          invc H.
          specialize (IHls H3).
          clear H3.
          unfold apM.
          apply bind_PreservesInvariant.
          apply bind_PreservesInvariant.
          apply ret_PreservesInvariant.
          intros s' x.
          apply liftM_PreservesInvariant.
          apply H2.
          intros s' x.
          apply liftM_PreservesInvariant.
          apply IHls.
      Qed.

      Instance zmap_sequence_PreservesInvariant
        {A: Type}
        (mv: ZMap.t (memM A)):
        forall s,
          (forall k v, ZMap.MapsTo k v mv -> forall s', PreservesInvariant s' v) ->
          PreservesInvariant s (zmap_sequence mv).
      Proof.
        intros s H.
        apply zmap_maps_to_elements_p in H.
        unfold zmap_sequence.
        break_let.
        apply bind_PreservesInvariant.
        -
          apply sequence_PreservesInvariant.
          generalize dependent (ZMap.elements (elt:=memM A) mv).
          intros ls H S.
          clear mv.
          rename l into lk, l0 into lv.
          apply Forall_nth.
          intros k v L.
          rewrite Forall_nth in H.
          specialize (H k (nth k lk 0, v)).

          break_let.
          autospecialize H.
          {
            rewrite <- split_length_r.
            rewrite S.
            cbn.
            assumption.
          }

          rewrite split_nth in Heqp.
          rewrite S in Heqp.
          cbn in *.
          tuple_inversion.
          assumption.
        -
          intros s' x.
          apply ret_PreservesInvariant.
      Qed.

      Instance zmap_mmapi_PreservesInvariant
        {A B : Type}
        (f : ZMap.key -> A -> memM B)
        (zm: ZMap.t A):
        forall s,
          (forall k x, forall s', PreservesInvariant s' (f k x)) ->
          PreservesInvariant s (@zmap_mmapi A B memM memM_monad f zm).
      Proof.
        intros s H.
        unfold zmap_mmapi.
        apply zmap_sequence_PreservesInvariant.
        intros k v H0.
        apply F.mapi_inv in H0.
        destruct H0 as [v' [k' [E [E1 M]]]].
        subst.
        apply H.
      Qed.

    End MemMwithInvariant.

  End CheriMemoryImplWithProofs.

  Module CheriMemoryImplWithProofsExe
    (SW: CerbSwitchesDefs)
  <: CheriMemoryImplWithProofs(SW).
    Include CheriMemoryImplWithProofs(SW).
  End CheriMemoryImplWithProofsExe.

  (* 1. removes all PNVI flavours
     2. Adds [SW_revocation INSTANT] and removes all other revocation mechanisms
   *)
  Module WithoutPNVISwitches.
    Definition get_switches (_:unit)
      :=
      ListSet.set_add cerb_switch_dec (SW_revocation INSTANT)
        (remove_Revocation
           (remove_PNVI (abst_get_switches tt))).
  End WithoutPNVISwitches.

  (* 1. removes all revocation mechanisms
     2. adds [SW_PNVI AE_UDI] and removes all other PNVI flavours *)
  Module WithPNVISwitches.
    Definition get_switches (_:unit)
      :=
      ListSet.set_add cerb_switch_dec (SW_PNVI AE_UDI)
        (remove_Revocation
           (remove_PNVI (abst_get_switches tt))).
  End WithPNVISwitches.


  (* This is pure CHERI memory model with instant revocation but without PNVI. *)
  Module CheriMemoryWithoutPNVI.
    Include CheriMemoryImplWithProofsExe(WithoutPNVISwitches).

    Opaque bind raise ret get put ErrorWithState.update fail fail_noloc serr2InternalErr liftM.
    Ltac preserves_step
      :=
      match goal with
      |[|- PreservesInvariant _ _ (bind get _)] => apply bind_get_PreservesInvariant
      |[|- PreservesInvariant _ _ (bind _ _)] => apply bind_PreservesInvariant
      |[|- PreservesInvariant _ _ (raise _)] => apply raise_PreservesInvariant
      |[|- PreservesInvariant _ _ (ret _)] => apply ret_PreservesInvariant
      |[|- PreservesInvariant _ _ get] => apply get_PreservesInvariant
      |[|- PreservesInvariant _ _ (put _) ] => apply put_PreservesInvariant
      |[|- PreservesInvariant _ _ (ErrorWithState.update _)] => apply update_PreservesInvariant
      |[|- PreservesInvariant _ _ (fail _ _)] => apply fail_PreservesInvariant
      |[|- PreservesInvariant _ _ (fail_noloc _)] => apply fail_noloc_PreservesInvariant
      |[|- PreservesInvariant _ _ (serr2InternalErr _)] => apply serr2InternalErr_PreservesInvariant
      |[|- PreservesInvariant _ _ (liftM _ _)] => apply liftM_PreservesInvariant
      |[|- PreservesInvariant _ _] => typeclasses eauto
      end ; intros.

    Ltac preserves_steps :=
      repeat (match goal with
              | |- PreservesInvariant _ _ (match _ with _ => _ end) => break_match_goal
              | |- PreservesInvariant _ _ _ => preserves_step
              | |- context [match _ with _ => _ end] => break_match_goal
              | |- context [if _ then _ else _] => break_match_goal
              end; intros; cbn).


    Lemma resolve_has_PNVI:
      has_PNVI (WithoutPNVISwitches.get_switches tt) = false.
    Proof.
      unfold WithoutPNVISwitches.get_switches.
      generalize (abst_get_switches tt) as l. intros l.
      unfold has_PNVI, remove_PNVI, remove_Revocation in *.
      apply Bool.not_true_is_false.
      intros E.
      apply Bool.Is_true_eq_left in E.
      apply list.existb_True in E.
      apply Exists_exists in E.
      destruct E as [x [H0 H1]].
      apply set_add_iff in H0.
      destruct H0.
      -
        subst.
        inversion H1.
      -
        apply filter_In in H.
        destruct H as [H2 H3].
        apply filter_In in H2.
        destruct H2 as [H4 H5].
        apply Bool.negb_true_iff in H5.
        rewrite H5 in H1.
        inversion H1.
    Qed.

    Lemma resolve_has_any_PNVI_flavour:
      forall p, has_switch (WithoutPNVISwitches.get_switches tt) (SW_PNVI p) = false.
    Proof.
      intros p.
      unfold WithoutPNVISwitches.get_switches.
      generalize (abst_get_switches tt) as l. intros.
      unfold has_switch, remove_PNVI, remove_Revocation in *.
      apply Bool.not_true_is_false.
      intros E.
      apply set_mem_correct1 in E.
      apply set_add_elim2 in E;[|auto].
      apply filter_In in E.
      destruct E as [E _].
      apply filter_In in E.
      destruct E as [_ E].
      cbn in E.
      congruence.
    Qed.

    Lemma resolve_has_INSTANT:
      has_switch (WithoutPNVISwitches.get_switches tt) (SW_revocation INSTANT) = true.
    Proof.
      unfold has_switch.
      unfold WithoutPNVISwitches.get_switches.
      apply set_mem_correct2.
      apply set_add_intro2.
      reflexivity.
    Qed.

    Lemma resolve_has_CORNUCOPIA:
      has_switch (WithoutPNVISwitches.get_switches tt) (SW_revocation CORNUCOPIA) = false.
    Proof.
      unfold WithoutPNVISwitches.get_switches.
      generalize (remove_PNVI (abst_get_switches tt)) as l.
      intros l.
      unfold has_switch.
      apply set_mem_complete2.
      intros E.
      apply set_add_elim in E.
      destruct E;[discriminate|].
      unfold remove_Revocation in H.
      apply filter_In in H.
      destruct H as [_ H].
      apply Bool.negb_true_iff in H.
      inv H.
    Qed.

    (* CheriMemoryWithoutPNVI memory invariant

     It is similar to "with PNVI" except: 1. Provenance should be
     always `Prov_disabled` 2. All tagged caps bounds should fit one
     of existing allocations

     It will work only for instant revocation. In the case of
     Cornucopia the invariant will be different.
     *)
    Definition mem_invariant
      (m: mem_state_r) : Prop
      :=
      let cm := m.(capmeta) in
      let bm := m.(bytemap) in
      let am := m.(allocations) in

      base_mem_invariant m
      /\
        (* All caps which are tagged according to capmeta must: *)
        (forall addr g,
            ZMap.MapsTo addr (true,g) cm ->
            (forall bs, fetch_bytes bm addr (sizeof_pointer MorelloImpl.get) = bs ->
                   (
                     (* Have same provenance and correct sequence bytes *)
                     split_bytes_ptr_spec Prov_disabled bs
                     /\ (exists c,
                           (* decode without error *)
                           decode_cap bs true c
                           (* with decoded bounds bounds fitting one of the allocations *)
                           /\ (exists a alloc_id, ZMap.MapsTo alloc_id a am /\
                                              (* We do not allow escaped pointers to local variables *)
                                              cap_bounds_within_alloc c a)
                       )
                   )
            )
        ).

    Lemma initial_mem_state_invariant:
      mem_invariant initial_mem_state.
    Proof.
      unfold initial_mem_state, mem_invariant.
      repeat split; cbn in *.
      -
        intros alloc_id a H.
        apply empty_mapsto_iff in H;
          contradiction.
      -
        intros alloc_id1 alloc_id2 a1 a2 NA H H0.
        apply empty_mapsto_iff in H;
          contradiction.
      -
        unfold zmap_forall_keys.
        intros k H.
        apply empty_in_iff in H;
          contradiction.
      -
        intros alloc_id H.
        apply empty_in_iff in H.
        tauto.
      -
        intros k a H.
        apply empty_mapsto_iff in H.
        tauto.
      -
        apply empty_mapsto_iff in H;
          contradiction.
      -
        apply empty_mapsto_iff in H;
          contradiction.
      -
        apply empty_mapsto_iff in H;
          contradiction.
    Qed.

    Lemma mem_state_after_ghost_tags_preserves:
      forall m addr size,
        mem_invariant m ->
        mem_invariant (mem_state_with_capmeta
                         (init_ghost_tags addr size (capmeta m))
                         m).
    Proof.
      intros m addr sz H.
      destruct H as [MIbase MIcap].
      destruct_base_mem_invariant MIbase.
      split.
      -
        (* base invariant *)
        clear MIcap.
        repeat split;auto.
        repeat split;auto.

        (* alignment proof *)
        intros a E.
        apply zmap_in_mapsto in E.
        destruct E as [tg E].
        unfold mem_state_with_capmeta in E.
        simpl in E.
        apply init_ghost_tags_spec in E.
        destruct E.
        +
          (* capmeta unchanged at [a] *)
          apply zmap_mapsto_in in H.
          apply Balign.
          apply H.
        +
          (* capmeta cleared *)
          destruct H as [H1 H2].
          apply H1.
      -
        intros a g E bs F.
        simpl in *.
        apply init_ghost_tags_spec in E.
        destruct E as [E | [A E]].
        +
          (* capmeta unchanged at [a] *)
          specialize (MIcap a g E bs F).
          apply MIcap.
        +
          inversion E.
    Qed.

    (*
      TODO: re-state and re-prove

    Instance allocator_PreservesInvariant (size align : Z):
      forall s,
        PreservesInvariant mem_invariant s (allocator size align).
    Proof.
      intros s.
      unfold allocator.
      preserves_step.
      apply bind_PreservesInvariant_same_state.
      -
        break_let.
        break_match_goal; same_state_steps.
      -
        intros x.
        apply put_PreservesInvariant'.
        intros I.
        apply mem_state_with_next_alloc_id_preserves,
          mem_state_with_last_address_preserves,
          mem_state_after_ghost_tags_preserves,I.
    Qed.
    Opaque allocator.
     *)

    Instance find_live_allocation_PreservesInvariant:
      forall s a, PreservesInvariant mem_invariant s
               (find_live_allocation a).
    Proof.
      intros s a.
      unfold find_live_allocation.
      preserves_steps.
    Qed.

    Instance maybe_revoke_pointer_PreservesInvariant
      allocation
      (st: mem_state)
      (addr: Z)
      (meta: (bool*CapGhostState)):

      forall s,
        PreservesInvariant mem_invariant s
          (maybe_revoke_pointer allocation st addr meta).
    Proof.
      intros s.
      unfold maybe_revoke_pointer.
      break_let.
      preserves_steps.
    Qed.

    (* relation of pointer before and afer revocaton (per [maybe_revoke_pointer] *)
    Inductive revoked_pointer_rel
      (a : allocation)
      (addr : ZMap.key)
      (bm: ZMap.t AbsByte)
      : (bool * CapGhostState) -> (bool * CapGhostState) -> Prop :=
    | revoked_pointer_rel_untagged: forall gs, revoked_pointer_rel a addr bm (false, gs) (false, gs)
    | revoked_pointer_rel_fetch_err: forall err gs,
        fetch_and_decode_cap bm addr true = inl err
        -> revoked_pointer_rel a addr bm (true, gs) (true, gs)
    | revoked_pointer_rel_out_of_scope: forall gs c,
        fetch_and_decode_cap bm addr true = inr c
        -> ~cap_bounds_within_alloc c a
        -> revoked_pointer_rel a addr bm (true, gs) (true, gs)
    | revoked_pointer_rel_revoked: forall gs c,
        fetch_and_decode_cap bm addr true = inr c
        -> cap_bounds_within_alloc c a
        -> revoked_pointer_rel a addr bm (true, gs) (false, {| tag_unspecified := false; bounds_unspecified := gs.(bounds_unspecified) |}).

    Lemma zmap_maybe_revoke_pointer_res_invariant:
      forall (a : allocation) (m : mem_state_r),
        mem_invariant m ->
        forall s : mem_state_r,
          mem_invariant s ->
          forall (s' : mem_state) (x : ZMap.t (bool * CapGhostState)),
            zmap_mmapi (maybe_revoke_pointer a m) (capmeta m) s = (s', inr x) -> mem_invariant s'.
    Proof.
      intros a m IM s IS s' x M.

      pose proof (zmap_mmapi_PreservesInvariant mem_invariant (maybe_revoke_pointer a m) (capmeta m) s) as P.
      autospecialize P.
      intros k x0.
      apply maybe_revoke_pointer_PreservesInvariant; auto.

      specialize (P IS).
      unfold post_exec_invariant, lift_sum_p in P.
      break_match.
      -
        unfold execErrS in Heqs0.
        break_let.
        break_match_hyp;[|inl_inr].
        inl_inr_inv.
        subst.
        unfold memM_monad in Heqp.
        rewrite M in Heqp.
        tuple_inversion.
      -
        unfold execErrS in Heqs0.
        break_let.
        Transparent ret raise.
        unfold ret, raise, Exception_either, Monad_either in Heqs0.
        Opaque ret raise.
        break_match_hyp;[inl_inr|].
        inl_inr_inv.
        subst.
        unfold memM_monad in Heqp.
        rewrite M in Heqp.
        tuple_inversion.
        assumption.
    Qed.

    Instance maybe_revoke_pointer_SameState
      (k : Z)
      (meta: bool * CapGhostState)
      (a : allocation)
      (m : mem_state):
      SameState (maybe_revoke_pointer a m k meta).
    Proof.
      Transparent ret raise bind serr2InternalErr.

      intros newmeta m0 m1 H.
      unfold maybe_revoke_pointer in H.
      unfold serr2InternalErr, ret, raise, memM_monad, Exception_errS, Exception_either, Monad_errS, Monad_either in H.
      break_let.
      break_match.
      tuple_inversion.
      reflexivity.
      unfold bind in H.
      break_let.
      break_match.
      tuple_inversion.
      break_match.
      tuple_inversion.
      reflexivity.
      tuple_inversion.
      break_match.
      repeat tuple_inversion.
      break_match.
      repeat tuple_inversion.
      repeat tuple_inversion.
      reflexivity.
      break_match.
      repeat tuple_inversion.
      repeat tuple_inversion.
      reflexivity.
      Opaque ret raise bind serr2InternalErr.
    Qed.

    Instance zmap_mmapi_maybe_revoke_pointer_same_state
      (a : allocation)
      (m: mem_state)
      (oldmeta : ZMap.t (bool * CapGhostState)):
      SameState (zmap_mmapi (maybe_revoke_pointer a m) oldmeta).
    Proof.
      typeclasses eauto.
    Qed.

    Lemma zmap_mmapi_maybe_revoke_pointer_spec
      (a : allocation)
      (s : mem_state)
      (oldmeta newmeta : ZMap.t (bool * CapGhostState)):
      zmap_mmapi (maybe_revoke_pointer a s) oldmeta s = (s, inr newmeta) ->
      zmap_relate_keys oldmeta newmeta (fun addr : ZMap.key => revoked_pointer_rel a addr s.(bytemap)).
    Proof.
      intros H.
      intros k.
      unfold zmap_mmapi in H.
      unfold zmap_sequence in H.
      break_let.
      remember (ZMap.mapi (maybe_revoke_pointer a s) oldmeta) as newmeta'.

      assert(zmap_relate_keys newmeta' newmeta
               (fun _ mx x =>
                  mx s = (s, inr x)
            )) as N.
      {
        clear k.
        rename l into lk, l0 into newcaps.
        Transparent bind ret serr2InternalErr raise.
        unfold memM_monad, Monad_errS, bind, ret, serr2InternalErr, Exception_errS, raise in H.
        Opaque bind ret serr2InternalErr raise.
        break_let.
        break_match_hyp;[inversion H|].
        tuple_inversion.
        intros k.
        remember (ZMap.mapi (maybe_revoke_pointer a s) oldmeta) as newmeta.

        rename l into rescaps, Heqp0 into SEQ, Heqp into SPL.
        remember (ZMap.elements (elt:=memM (bool * CapGhostState)) newmeta) as enewmeta eqn:E.
        (* end of prep *)
        pose proof (@split_nth  _ _ enewmeta) as N.
        replace (fst (split enewmeta)) with lk in N by (rewrite SPL;reflexivity).
        replace (snd (split enewmeta)) with newcaps in N by (rewrite SPL;reflexivity).

        (* will need lengths later *)
        pose proof (@sequence_len_errS _ _ _ _ _ _ _ SEQ) as RL.
        pose proof (split_length_l enewmeta) as KL.
        rewrite SPL in KL.
        cbn in KL.
        pose proof (split_length_r enewmeta) as KR.
        rewrite SPL in KR.
        cbn in KR.

        (* end prep *)

        apply sequence_spec_same_state_memM in SEQ.
        -
          destruct (@In_dec _ newmeta k) as [I|NI].
          +
            (* key originally exists *)
            left.
            apply zmap_in_mapsto in I.
            destruct I as [v1 I].
            exists v1.

            assert(ZMap.MapsTo k v1 newmeta) as I1 by assumption.
            rewrite Heqnewmeta in I1.
            apply mapi_inv in I1.
            destruct I1 as [v2 [k' [I3 [I4 I5]]]].
            subst k'.

            pose proof (ZMap.elements_1 I) as H.
            rewrite <- E in H.
            apply InA_alt in H.
            destruct H as [(addr,v2') [H1 H2]].

            unfold ZMap.eq_key_elt, ZMap.Raw.Proofs.PX.eqke in H1.
            destruct H1 as [T1 T2].
            cbn in T1, T2.
            subst k v2'.

            apply In_nth with (d:=(addr, v1)) in H2.
            destruct H2 as [n [H2 H3]].
            specialize (N n (addr, v1)).
            rewrite H3 in N.
            cbn in N.
            inversion N.
            rewrite <- H1, <- H0.

            apply list.Forall2_lookup_l with (i:=n) (x:=v1) in SEQ.
            2:{
              destruct (list.nth_lookup_or_length newcaps n v1) as [L|NL].
              ++ rewrite <-H1 in L. apply L.
              ++ lia.
            }

            destruct SEQ as [v2' [A1 A2]].

            exists v2'.
            split;[apply I|].
            split.
            *
              apply ZMap.ZP.of_list_1.
              --
                apply combine_eq_key_NoDupA.
                pose proof (ZMap.elements_3w newmeta) as NDM.
                pose proof (split_eq_key_NoDup _ _ _ SPL).
                rewrite E in H.
                specialize (H NDM).
                apply H.
              --
                pose proof (combine_length lk rescaps ) as CL.
                remember (combine lk rescaps) as res eqn:C.
                symmetry in C.
                apply combine_spec in C.
                ++
                  assert(In addr lk) as IK.
                  {
                    rewrite H0.
                    apply nth_In.
                    lia.
                  }
                  clear - C A1 H0 RL KL KR H2 CL.
                  rewrite MachineWord.MachineWord.nth_error_lookup in A1.
                  assert(nth_error lk n = Some addr).
                  {
                    rewrite H0.
                    eapply nth_error_nth'.
                    lia.
                  }
                  apply InA_alt.
                  exists (addr, v2').
                  split.
                  reflexivity.
                  eapply split_eq_key_elt_nth in C; eauto.
                  apply nth_error_nth with (d:=(addr, v2')) in C.
                  setoid_rewrite <- C.
                  apply nth_In.
                  clear -CL H2 RL KL KR.
                  unfold memM, ZMap.key in *.
                  lia.
                ++
                  clear - RL KL KR.
                  unfold memM in *.
                  lia.
            *
              apply A2.
          +
            (* key does not exists *)
            right.
            split;[assumption|].
            pose proof (ZMap.elements_3w newmeta) as NDM.
            pose proof (split_eq_key_NoDup _ _ _ SPL).
            rewrite E in H.
            specialize (H NDM).
            intros C.
            destruct C as [v C].
            apply ZMap.ZP.of_list_1 in C;[|apply combine_eq_key_NoDupA, H].
            apply InA_eq_key_combine in C.
            contradict NI.
            clear - E SPL C NDM.
            subst enewmeta.
            replace lk with (fst (split (ZMap.elements (elt:=memM (bool * CapGhostState)) newmeta))) in C.
            apply In_zmap_elements_split_zmap_in, C.
            rewrite SPL.
            reflexivity.
        -
          clear k. (* used in previous goal *)
          apply Forall_nth.
          intros k d H.
          (* [k] is index, not address *)
          assert(option.is_Some (base.lookup k enewmeta)) as ES.
          {
            apply list.lookup_lt_is_Some.
            lia.
          }
          unfold option.is_Some in ES.
          destruct ES as [[addr v1] ES].
          specialize (N k (addr,v1)).

          (* TODO maybe make this lemma *)
          assert (ZMap.MapsTo addr v1 newmeta).
          {
            apply ZMap.elements_2.
            rewrite <- E.
            clear -ES.
            apply list.elem_of_list_lookup_2 in ES.
            apply base.elem_of_list_In in ES.
            apply InA_alt.
            exists (addr,v1).
            split.
            -
              unfold ZMap.eq_key_elt, ZMap.Raw.Proofs.PX.eqke.
              split; reflexivity.
            -
              assumption.
          }
          rewrite Heqnewmeta in H0.
          apply mapi_inv in H0.
          destruct H0 as [v2 [addr' [E2 [E3 E4]]]].
          subst addr'.
          cbn in N.

          (* cleanup nth mess *)
          rewrite nth_indep with (d':=v1) by auto.
          rewrite (list.nth_lookup_Some _ _ _ _ ES) in N.
          clear ES.
          inversion N.
          clear N.
          rewrite <- H2, <- H2, E3.
          apply maybe_revoke_pointer_SameState.
      }

      clear H Heqp.
      pose proof (zmap_relate_keys_same_keys _ _ _ N k) as SN.
      destruct (@In_dec _ oldmeta k) as [I|NI].
      -
        (* key originally exists *)
        left.
        apply zmap_in_mapsto in I.
        destruct I as [v1 I].
        exists v1.
        pose proof (@ZMap.mapi_1 _ _ _ _ _ (maybe_revoke_pointer a s) I) as [y [YH Z]].
        subst y.
        rewrite <- Heqnewmeta' in Z.
        specialize (N k).
        destruct N as [N|[NN1 NN2]].
        +
          destruct N as [v1' [v2 [N1 [N2 N3]]]].
          apply (MapsTo_fun N1) in Z.
          subst v1'.
          exists v2.
          split;[apply I|].
          split;[apply N2|].
          clear - N3.
          unfold maybe_revoke_pointer in N3.
          break_let.
          break_match.
          *
            Transparent ret.
            unfold memM_monad, Monad_errS, ret in N3.
            Opaque ret.
            tuple_inversion.
            destruct b. inversion Heqb0.
            constructor.
          *
            destruct b;[|inversion Heqb0].
            clear Heqb0.
            Transparent bind ret serr2InternalErr raise.
            unfold memM_monad, Monad_errS, bind, ret, serr2InternalErr, Exception_errS, raise in N3.
            Opaque bind ret serr2InternalErr raise.
            break_let.
            subst.
            destruct s0;[inversion N3|].
            destruct (fetch_and_decode_cap (bytemap s) k true) eqn:FF;[inversion Heqp0|].
            Transparent ret.
            unfold memM_monad, Monad_errS, ret in Heqp0.
            Opaque ret.
            tuple_inversion.
            break_match.
            --
              apply cap_bounds_within_alloc_true in Heqb.
              tuple_inversion.
              eapply (revoked_pointer_rel_revoked _ _ _ _ t);eauto.
            --
              tuple_inversion.
              apply cap_bounds_within_alloc_false in Heqb.
              eapply (revoked_pointer_rel_out_of_scope _ _ _ _ t);eauto.
        +
          contradict NN1.
          exists (maybe_revoke_pointer a s k v1).
          assumption.
      -
        right.
        assert(~ (exists v : bool * CapGhostState, ZMap.MapsTo k v oldmeta)) as NM.
        intros [v C].
        apply zmap_mapsto_in in C.
        congruence.
        split;[apply NM|].
        intros [v C].
        apply zmap_mapsto_in in C.
        apply SN in C.
        contradict NM.
        clear - C Heqnewmeta'.
        subst.
        apply ZMap.mapi_2 in C.
        apply C.
    Qed.

    (* This function stands out because its state is subtly but deeply
       connected to the return value. We couldn't use our usual preservation
       step lemmas and had to resort to brute-forcing our way through.  *)
    Instance revoke_pointers_PreservesInvariant:
      forall s a, PreservesInvariant mem_invariant s (revoke_pointers a).
    Proof.
      intros s a.
      unfold revoke_pointers.
      intros H.
      Transparent ret raise bind get.
      unfold post_exec_invariant, execErrS, evalErrS, lift_sum_p.
      break_let.
      break_match.
      trivial.
      break_match_hyp.
      inl_inr.
      inl_inr_inv.
      subst.

      unfold memM_monad, Monad_errS, State_errS, ret, bind, get in Heqp.
      repeat break_let.
      break_match_hyp.
      tuple_inversion.
      break_let.
      break_match_hyp;
        tuple_inversion.

      destruct u0.
      rename Heqp1 into U, t into newmeta.
      apply update_mem_state_spec in U.

      (* [maybe_revoke_pointer] does not change state *)
      assert(SM0: s = m).
      {
        eapply zmap_mmapi_maybe_revoke_pointer_same_state.
        eauto.
      }
      subst m.

      apply(zmap_mmapi_maybe_revoke_pointer_spec a s (capmeta s) newmeta) in Heqp0.
      rename Heqp0 into R.
      unfold mem_state_with_capmeta in U.

      destruct H as [Sbase Scap].
      destruct_base_mem_invariant Sbase.
      destruct s; cbn in *.
      invc U.
      split.
      -
        (* base_mem_invariant *)
        repeat split;auto.

        clear - Balign R.
        cbn.
        intros k I.
        specialize (Balign k).
        specialize (R k).
        destruct R as [[v1 [v2 [M1 [M2 R]]]]|[NR0 NR1]].
        +
          apply Balign.
          eapply zmap_mapsto_in.
          eauto.
        +
          contradict NR1.
          eapply zmap_in_mapsto in I.
          apply I.
      -
        clear Bdead Bnooverlap Balign.
        intros addr g H1 bs H0.
        specialize (Scap addr g).
        specialize (R addr).
        cbn in *.
        destruct R as [[v1 [v2 [M1 [M2 R]]]]|[NR0 NR1]].
        --
          pose proof (MapsTo_fun M2 H1).
          subst v2.
          (* both keys present *)
          invc R.
          ++
            (* ghost states are same *)
            specialize (Scap M1).
            remember (fetch_bytes bytemap0 addr (sizeof_pointer MorelloImpl.get)) as bs.
            specialize (Scap bs).
            autospecialize Scap.
            reflexivity.
            auto.
          ++
            (* revoked *)
            specialize (Scap M1).
            remember (fetch_bytes bytemap0 addr (sizeof_pointer MorelloImpl.get)) as bs.
            specialize (Scap bs).
            autospecialize Scap.
            reflexivity.
            apply Scap.
        --
          (* both keys are absent *)
          contradict NR1.
          eexists.
          eauto.
          Opaque ret raise bind get.
    Qed.

    Lemma no_caps_pointing_to_alloc
      (s s' : mem_state_r)
      (alloc : allocation)
      (addr : ZMap.key)
      (g : CapGhostState)
      (bs : list AbsByte)
      (c : Capability_GS.t)
      :
      revoke_pointers alloc s = (s', inr tt) ->
      ZMap.MapsTo addr (true, g) (capmeta s') ->
      fetch_bytes (bytemap s') addr (sizeof_pointer MorelloImpl.get) = bs ->
      split_bytes_ptr_spec Prov_disabled bs ->
      decode_cap bs true c -> ~ cap_bounds_within_alloc c alloc.
    Proof.
      intros R M F S D.
      unfold revoke_pointers in R.
      Transparent ret bind get.
      unfold memM_monad, Monad_errS, State_errS, ret, bind, get in R.
      Opaque ret bind get.
      break_let.
      break_match_hyp;[inversion R|].
      break_let.
      break_match_hyp;[inversion R|].
      destruct u.
      tuple_inversion.

      pose proof (zmap_mmapi_maybe_revoke_pointer_same_state _ _ _ _ _ _ Heqp) as E.
      subst m.

      apply update_state_capmeta in Heqp0.
      destruct Heqp0 as [E1 E2].
      subst.
      generalize dependent (capmeta s').
      intros cm Z M.

      apply zmap_mmapi_maybe_revoke_pointer_spec in Z.
      specialize (Z addr).
      invc Z.
      -
        (* both exists in [campeta s] and [cm] *)
        destruct H as [g1 [g2 [H1 [H2 R]]]].
        pose proof (MapsTo_fun M H2).
        subst g2. clear H2.
        invc R.
        +
          (* fetch error - not possible *)
          exfalso.
          rewrite E2 in *.
          clear E2 s'.
          assert (fetch_and_decode_cap (bytemap s) addr true = inr c).
          apply fetch_and_decode_cap_success;auto.
          congruence.
        +

          rewrite E2 in *.
          clear E2 s'.
          assert (fetch_and_decode_cap (bytemap s) addr true = inr c).
          apply fetch_and_decode_cap_success;auto.
          rewrite H in H0.
          inl_inr_inv.
          assumption.
      -
        (* not in capmeta  *)
        destruct H as [H1 H2].
        contradict H2.
        exists (true, g).
        apply M.
    Qed.

    Lemma remove_revoked_allocation_preserves
      (s s' s'': mem_state_r)
      (alloc_id : Z)
      (alloc : allocation)
      (AM: ZMap.MapsTo alloc_id alloc (allocations s))
      (IS: mem_invariant s)
      (IS': mem_invariant s'):

      revoke_pointers alloc s = (s', inr tt)
      -> remove_allocation alloc_id s' = (s'', inr tt)
      ->  mem_invariant s''.
    Proof.
      intros RE RM.

      Transparent bind get put ErrorWithState.update.
      unfold remove_allocation, ErrorWithState.update in RM.
      unfold bind, get, put, Monad_errS, State_errS in RM.
      Opaque bind get put ErrorWithState.update.
      tuple_inversion.

      destruct IS' as [ISbase' IScap']. clear IS.
      (* destruct_base_mem_invariant Sbase. *)
      split;cbn.
      -
        (* base *)
        clear IScap' AM RE.
        destruct_base_mem_invariant ISbase'.
        repeat split; cbn.
        +
          intros alloc_id0 a H.
          apply ZMap.remove_3 in H.
          eapply Bdead;eauto.
        +
          intros alloc_id1 alloc_id2 a1 a2 NA H H0.
          apply ZMap.remove_3 in H0, H.
          eapply Bnooverlap.
          eauto.
          eauto.
          eauto.
        +
          apply Balign.
        +
          intros alloc_id' H.
          destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
          *
            apply (ZMap.remove_1 E) in H.
            inv H.
          *
            rewrite (remove_neq_in_iff _ NE) in H.
            eauto.
        +
          apply zmap_forall_remove.
          auto.
      -
        clear ISbase'.
        intros addr g A bs F.
        specialize (IScap' addr g A bs F).
        destruct IScap' as [IScap1' [c [IScap3' [alloc' [alloc_id' [IScap4' IScap5']]]]]].
        split.
        apply IScap1'.
        exists c.
        split;auto.
        exists alloc'.
        destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
        +
          subst alloc_id'.
          (* [alloc_id] is being removed *)
          exfalso.

          assert(alloc = alloc').
          {
            clear - RE AM IScap4'.
            unfold revoke_pointers in RE.
            Transparent bind get ret put ErrorWithState.update.
            unfold mem_state_with_capmeta, ErrorWithState.update, bind, get, ret, put, memM_monad, Monad_errS, State_errS in RE.
            Opaque bind get ret put ErrorWithState.update.
            break_let.

            break_match_hyp.
            inv RE.
            apply zmap_mmapi_maybe_revoke_pointer_same_state in Heqp.
            subst m.
            subst s0.
            destruct s.
            cbn in *.
            tuple_inversion.
            cbn in *.
            eapply MapsTo_fun; eauto.
          }
          subst alloc'.
          (*
            - alloc_id is present in [s] and [s']
            - we remove it from [s'] via [Zmap.remove] in the goal
            - after [revoke_pointers] there is no tagged pointers in [s'] with bounds within this alloc
            - [revoke_pointers] does not change [allocatons]. They only touch [capmeta]
           *)
          contradict IScap5'.
          eapply no_caps_pointing_to_alloc; eauto.
        +
          exists alloc_id'.
          split;[|auto].
          apply ZMap.remove_2;auto.
    Qed.

    Instance kill_PreservesInvariant
      (loc : location_ocaml)
      (is_dyn : bool)
      (ptr : pointer_value_indt)
      :
      forall s,
        PreservesInvariant mem_invariant s (kill loc is_dyn ptr).
    Proof.
      unfold kill.
      rewrite resolve_has_PNVI, resolve_has_INSTANT.
      destruct ptr.
      destruct p eqn:P; intros.
      2,3: preserves_steps.
      break_match_goal;cbn;[preserves_step|].
      break_match_goal;cbn;[preserves_step|].
      apply bind_PreservesInvariant_value.
      intros H s' x H0.

      pose proof (find_live_allocation_SameState (Capability_GS.cap_get_value t)) as H2.
      specialize (H2 _ _ _ H0).
      subst s'.
      split;[assumption|].
      pose proof (find_live_allocation_PreservesInvariant s (Capability_GS.cap_get_value t)) as A.
      specialize (A H).
      unfold post_exec_invariant, lift_sum_p in A.
      break_match_hyp.
      -
        clear - H0 Heqs0.
        unfold execErrS in Heqs0.
        break_let.
        tuple_inversion.
        inl_inr.
      -
        unfold execErrS in Heqs0.
        break_let.
        tuple_inversion.
        inl_inr_inv.
        subst m.
        clear H.
        break_match;[|preserves_steps].
        break_let.
        apply bind_PreservesInvariant_same_state.
        repeat break_match; typeclasses eauto.
        intros u. destruct u.
        apply bind_PreservesInvariant_same_state.
        repeat break_match; typeclasses eauto.
        intros u. destruct u.
        apply bind_PreservesInvariant_full.
        intros _ s' x0 H0.
        pose proof (revoke_pointers_PreservesInvariant s a) as R.
        specialize (R A).
        unfold post_exec_invariant, lift_sum_p in R.
        break_match_hyp.
        +
          unfold execErrS in Heqs0.
          break_let.
          tuple_inversion.
          inl_inr.
        +
          unfold execErrS in Heqs0.
          break_let.
          tuple_inversion.
          inl_inr_inv.
          subst m.
          destruct x0.
          rename a into alloc, z into alloc_id.
          apply find_live_allocation_res_consistent in Heqp0.
          (* It looks like we have everything we need here *)
          unfold post_exec_invariant, lift_sum_p.
          break_match_goal;[trivial|].

          unfold execErrS in Heqs0.
          break_let.
          break_match_hyp;[inl_inr|inl_inr_inv].
          subst.
          destruct u.
          eapply remove_revoked_allocation_preserves; eauto.
    Qed.
    Opaque kill.

    Instance find_cap_allocation_SameState:
      forall x, SameState (find_cap_allocation x).
    Proof.
      intros x.
      unfold find_cap_allocation.
      same_state_steps.
    Qed.

    Instance is_dead_allocation_SameState:
      forall x, SameState (is_dead_allocation x).
    Proof.
      intros x.
      unfold is_dead_allocation.
      same_state_steps.
    Qed.

    Instance get_allocation_SameState:
      forall x, SameState (get_allocation x).
    Proof.
      intros x.
      unfold get_allocation.
      same_state_steps.
    Qed.

    Instance is_within_bound_SameState:
      forall x0 x1 x2, SameState (is_within_bound x0 x1 x2).
    Proof.
      intros x0 x1 x2.
      unfold is_within_bound.
      same_state_steps.
    Qed.

    Instance is_atomic_member_access_SameState:
      forall x0 x1 x2, SameState (is_atomic_member_access x0 x1 x2).
    Proof.
      intros x0 x1 x2.
      unfold is_atomic_member_access.
      same_state_steps.
    Qed.

    Instance cap_check_SameState:
      forall x0 x1 x2 x3 x4, SameState (cap_check x0 x1 x2 x3 x4).
    Proof.
      intros x0 x1 x2 x3 x4.
      unfold cap_check.
      same_state_steps.
    Qed.

    Instance mem_value_strip_err_SameState:
      forall loc v, SameState (mem_value_strip_err loc v).
    Proof.
      intros loc v.
      induction v; same_state_steps.
      -
        cbn.
        same_state_steps.
        assumption.
      -
        cbn.
        same_state_steps.
        cbn.
        apply Forall_forall.
        intros x H0.
        repeat break_let.
        same_state_steps.
        eapply Forall_forall with (x:=x) in H.
        repeat break_let.
        tuple_inversion.
        assumption.
        subst x.
        assumption.
    Qed.

    (* Without PNVI [load] does not modify state.  NB: it will not be
       the case in the presence of PNVI, because of
       [expose_allocations] *)
    Instance load_SameState
      (loc: location_ocaml)
      (ty: CoqCtype.ctype)
      (p: pointer_value)
      :
      SameState (load loc ty p).
    Proof.
      unfold load.
      repeat rewrite resolve_has_any_PNVI_flavour.
      same_state_steps; cbn in *; congruence.
    Qed.

    Instance eq_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (eq_ptrval loc ptr1 ptr2).
    Proof.
      unfold eq_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance ne_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (ne_ptrval loc ptr1 ptr2).
    Proof.
      unfold ne_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance lt_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (lt_ptrval loc ptr1 ptr2).
    Proof.
      unfold lt_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance gt_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (gt_ptrval loc ptr1 ptr2).
    Proof.
      unfold gt_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance le_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (le_ptrval loc ptr1 ptr2).
    Proof.
      unfold le_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance ge_ptrval_SameState
      (loc : location_ocaml)
      (ptr1 ptr2 : pointer_value) :
      SameState (ge_ptrval loc ptr1 ptr2).
    Proof.
      unfold ge_ptrval.
      repeat break_let.
      same_state_steps.
    Qed.

    Instance diff_ptrval_SameState
      (loc : location_ocaml)
      (diff_ty : CoqCtype.ctype) (ptrval1 ptrval2 : pointer_value):
      SameState(diff_ptrval loc diff_ty ptrval1 ptrval2).
    Proof.
      unfold diff_ptrval.
      same_state_steps.
    Qed.

    Instance update_prefix_PreservesInvariant:
      forall s x, PreservesInvariant mem_invariant s (update_prefix x).
    Proof.
      intros s x.
      unfold update_prefix.
      preserves_steps.
      subst.
      remember (zmap_update _ _ _) as newallocations.
      unfold mem_state_with_allocations.
      destruct H as [MIbase MIcap].
      destruct_base_mem_invariant MIbase.
      split.
      -
        (* base invariant *)
        clear MIcap.
        unfold zmap_update.
        repeat split;cbn.
        +
          (* Bdead *)
          clear - Bdead Heqnewallocations.
          generalize dependent (allocations m0).
          clear m0.
          intros old Bdead Heqnewallocations alloc_id a H.
          rename s0 into alloc_id'.
          subst.
          destruct (Z.eq_dec alloc_id alloc_id').
          *
            specialize (Bdead alloc_id).
            subst alloc_id'.
            destruct (ZMap.find alloc_id old) eqn:F.
            --
              apply ZMap.find_2 in F.
              specialize (Bdead a0 F).
              pose proof (zmap_update_MapsTo_update_at_k F H).
              clear H F.
              cbn in H0.
              invc H0.
              cbn.
              assumption.
            --
              apply not_find_in_iff in F.
              clear Bdead.
              pose proof (zmap_update_MapsTo_new_at_k F H).
              clear H F.
              cbn in H0.
              inversion H0.
          *
            apply zmap_update_MapsTo_not_at_k in H;auto.
            eapply Bdead; eauto.
        +
          (* Bnooverlap *)
          clear Bdead Balign Bnextallocid Blastaddr.
          generalize dependent (allocations m0).
          clear m0.
          intros old Bnooverlap Heqnewallocations alloc_id1 alloc_id2 a1 a2 NA M1 M2.
          rename s0 into alloc_id.
          subst.

          Ltac solve_cases :=
            repeat match goal with
              (* absurd cases *)
              | [H: ZMap.find ?alloc_id _ = None, M: ZMap.MapsTo ?alloc_id _ _ |- _]
                =>
                  let X := fresh "X" in
                  apply not_find_in_iff in H;
                  pose proof (zmap_update_MapsTo_new_at_k H M) as X;
                  cbn in X; inversion X
              | [H: ZMap.find ?alloc_id _ = Some _, M: ZMap.MapsTo ?alloc_id _ _ |- _]
                =>
                  let X := fresh "X" in
                  apply ZMap.find_2 in H;
                  pose proof (zmap_update_MapsTo_update_at_k H M) as X;
                  cbn in X;
                  clear M;
                  some_inv
              | [H:  ?alloc_id' <> ?alloc_id, M: ZMap.MapsTo ?alloc_id' _ (zmap_update ?alloc_id _ _) |- _]
                =>
                  apply zmap_update_MapsTo_not_at_k in M;auto
              end.

          destruct (Z.eq_dec alloc_id1 alloc_id), (Z.eq_dec alloc_id2 alloc_id),
            (ZMap.find alloc_id1 old) eqn:F1, (ZMap.find alloc_id2 old) eqn:F2; subst ; try solve_cases.

          all:
            unfold allocations_do_no_overlap in *;
            unfold allocation_with_prefix;
            cbn; eauto.
        +
          (* Balign *)
          auto.
        +
          (* Bnextallocid *)
          clear - Bnextallocid Heqnewallocations.
          subst newallocations.
          rename s0 into alloc_id'.
          intros alloc_id.
          destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
          *
            subst alloc_id'.
            intros H.
            unfold zmap_update in H.
            repeat break_match_hyp;try some_none; try some_inv.
            --
              apply Bnextallocid.
              apply in_find_iff.
              rewrite Heqo0.
              auto.
            --
              apply ZMap.remove_1 in H.
              tauto.
              reflexivity.
          *
            intros H.
            unfold zmap_update in H.
            repeat break_match_hyp;try some_none; try some_inv.
            --
              apply Bnextallocid.
              apply add_neq_in_iff in H;auto.
              apply remove_neq_in_iff in H;auto.
            --
              apply remove_neq_in_iff in H;auto.
        +
          (* Blastaddr *)
          clear - Blastaddr Heqnewallocations.
          subst newallocations.
          rename s0 into alloc_id'.
          intros alloc_id a.
          destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
          *
            subst alloc_id'.
            intros H.
            unfold zmap_update in H.
            repeat break_match_hyp;try some_none; try some_inv.
            --
              apply ZMap.find_2 in Heqo0.
              apply add_mapsto_iff in H.
              destruct H;[|destruct H; congruence].
              destruct H as [_ H3].
              subst a0.
              specialize (Blastaddr alloc_id a1 Heqo0).
              unfold allocation_with_prefix in H1.
              destruct a.
              cbn in *.
              invc H1.
              auto.
            --
              apply zmap_mapsto_in in H.
              apply ZMap.remove_1 in H.
              tauto.
              reflexivity.
          *
            intros H.
            unfold zmap_update in H.
            repeat break_match_hyp;try some_none; try some_inv.
            --
              apply add_neq_mapsto_iff in H; auto.
              apply remove_neq_mapsto_iff in H; auto.
              eauto.
            --
              apply remove_neq_mapsto_iff in H; auto.
              eauto.
      -
        rename c into ty, s0 into alloc_id.
        clear Bdead Bnooverlap Balign.
        cbn.
        intros addr g H bs H0.
        specialize (MIcap addr g H bs H0).
        destruct MIcap as [SB [c [D [a [alloc_id' [M B]]]]]].
        split;[assumption|].
        exists c.
        split;[assumption|].
        destruct (Z.eq_dec alloc_id alloc_id').
        +
          subst alloc_id'.
          subst newallocations.
          epose proof (zmap_update_MapsTo_update_at_k' M).
          eexists.
          eexists.
          split.
          eapply H1.
          eauto.
          eauto.
        +
          subst newallocations.
          eapply zmap_update_MapsTo_not_at_k in M.
          eexists.
          eexists.
          split.
          eauto.
          eauto.
          eauto.
    Qed.

    Instance isWellAligned_ptrval_SameState
      (ref_ty: CoqCtype.ctype)
      (ptrval: pointer_value):
      SameState (isWellAligned_ptrval ref_ty ptrval).
    Proof.
      unfold isWellAligned_ptrval.
      same_state_steps.
    Qed.

    Instance validForDeref_ptrval_SameState
      (ref_ty: CoqCtype.ctype)
      (ptrval: pointer_value):
      SameState (validForDeref_ptrval ref_ty ptrval).
    Proof.
      unfold validForDeref_ptrval.
      same_state_steps.
    Qed.

    (* Without PNVI [ptrfromint] does not modify state. NB: it will not be
       the case in the presence of PNVI, because of
       [expose_allocation] *)
  Instance ptrfromint_SameState
    (loc : location_ocaml)
    (int_ty : CoqIntegerType.integerType)
    (ref_ty : CoqCtype.ctype)
    (int_v : integer_value):
    SameState (ptrfromint loc int_ty ref_ty int_v).
  Proof.
    unfold ptrfromint.
    same_state_steps.
  Qed.

  Instance intfromptr_SameState
    (loc : location_ocaml)
    (unused : CoqCtype.ctype)
    (ity: CoqIntegerType.integerType)
    (ptr: pointer_value):
    SameState (intfromptr loc unused ity ptr).
  Proof.
    intros.
    unfold intfromptr.
    repeat rewrite resolve_has_any_PNVI_flavour.
    same_state_steps;lia.
  Qed.

  Instance eff_array_shift_ptrval_SameState
    (loc : location_ocaml)
    (ptrval : pointer_value)
    (ty : CoqCtype.ctype)
    (ival_int : integer_value):
    SameState (eff_array_shift_ptrval loc ptrval ty ival_int).
  Proof.
    unfold eff_array_shift_ptrval.
    same_state_steps.
  Qed.

  Instance eff_member_shift_ptrval_SameState
    (loc : location_ocaml)
    (ptr : pointer_value)
    (tag_sym: CoqSymbol.sym)
    (memb_ident: CoqSymbol.identifier):
    SameState (eff_member_shift_ptrval loc ptr tag_sym memb_ident).
  Proof.
    unfold eff_member_shift_ptrval.
    break_let.
    same_state_steps.
  Qed.

  Instance copy_alloc_id_SameState
    (ival : integer_value)
    (ptrval : pointer_value):
    SameState  (copy_alloc_id ival ptrval).
  Proof.
    unfold copy_alloc_id.
    same_state_steps.
  Qed.

  Instance sequencePoint_SameState
    : SameState  (sequencePoint).
  Proof.
    unfold sequencePoint.
    same_state_steps.
  Qed.

  Instance allocate_object_PreservesInvariant
    (tid:MemCommonExe.thread_id)
    (pref:CoqSymbol.prefix)
    (int_val:integer_value)
    (ty:CoqCtype.ctype)
    (init_opt:option mem_value)
    :
    forall s, PreservesInvariant mem_invariant s (allocate_object tid pref int_val ty init_opt).
  Proof.
    intros s.
    unfold allocate_object.
    (* TODO: postponed until I figure out readonly logic and re-prove `allocator` *)
  Admitted.

  Instance allocate_region_PreservesInvariant
    (tid : MemCommonExe.thread_id)
    (pref : CoqSymbol.prefix)
    (align_int : integer_value)
    (size_int : integer_value)
    :
    forall s, PreservesInvariant mem_invariant s (allocate_region tid pref align_int size_int).
  Proof.
    intros s.
    unfold allocate_region.
    (* TODO: postponed until I re-prove `allocator` *)
  Admitted.

  Instance store_PreservesInvariant
    (loc : location_ocaml)
    (cty : CoqCtype.ctype)
    (is_locking : bool)
    (ptr : pointer_value)
    (mval : mem_value):
    forall s, PreservesInvariant mem_invariant s (store loc cty is_locking ptr mval).
  Proof.
    (* TODO: postponed until I figure out `is_locking` logic*)
  Admitted.

  (** Helper predicate for [memcpy] correctness assumption. Two memory
      regions of size [n] pointed by 2 pointers do not overlap. It is
      only defined for [PVconcrete].
   *)
  Inductive mempcpy_args_sane: pointer_value -> pointer_value -> Z -> Prop
    :=
  | ptrval_overlap_concrete: forall c1 c2 n a1 a2 p1 p2,
      a1 = AddressValue.to_Z (Capability_GS.cap_get_value c1) ->
      a2 = AddressValue.to_Z (Capability_GS.cap_get_value c2) ->
      0 <= n ->
      Z.abs (a1-a2) >= n ->
      mempcpy_args_sane (PV p1 (PVconcrete c1)) (PV p2 (PVconcrete c2)) n .

  Fact memcpy_PreservesInvariant_fact
    {addr1 addr2 : Z}
    {m : mem_state_r}
    {p : bool * CapGhostState}
    {H: mem_invariant m}:

    (ZMap.find (elt:=bool * CapGhostState) addr2 (capmeta m) = Some p) ->
    (is_pointer_algined addr1 = true) ->
    (fetch_bytes (bytemap m) addr1 (sizeof_pointer MorelloImpl.get) = fetch_bytes (bytemap m) addr2 (sizeof_pointer MorelloImpl.get))  ->
    mem_invariant (mem_state_with_capmeta (ZMap.add addr1 p (capmeta m)) m).
  Proof.
    intros F A B.
    destruct H as [MIbase MIcap].
    unfold mem_invariant.
    split.
    -
      (* base *)
      clear MIcap.
      destruct_base_mem_invariant MIbase.
      repeat split; auto.
      cbn.
      unfold zmap_forall_keys in *.
      intros k H.
      destruct (Z.eq_dec k addr1) as [E|NE].
      +
        subst.
        unfold is_pointer_algined in A.
        lia.
      +
        apply add_neq_in_iff in H;[auto|lia].
    -
      clear MIbase A.
      destruct (Z.eq_dec addr1 addr2) as [E|NE].
      +
        subst addr2.
        cbn in *.
        intros k.
        destruct (Z.eq_dec k addr1) as [KE|KNE].
        *
          subst addr1.
          intros g H bs H0.
          apply find_mapsto_iff in F.
          apply add_mapsto_iff in H.
          destruct H;[|lia].
          destruct H as [_ P].
          subst p.
          specialize (MIcap k g F bs H0).
          auto.
        *
          intros g H bs H0.
          apply find_mapsto_iff in F.
          apply ZMap.add_3 in H;[|auto].
          specialize (MIcap k g H bs H0).
          auto.
      +
        intros k g H bs H0.
        cbn in *.

        destruct (Z.eq_dec k addr1) as [KE1|KNE1].
        *
          subst addr1.
          apply find_mapsto_iff in F.
          apply add_mapsto_iff in H.
          destruct H;[|lia].
          destruct H as [_ P].
          subst p.
          rewrite B in H0.
          specialize (MIcap addr2 g F bs H0).
          auto.
        *
          apply ZMap.add_3 in H;[|auto].
          --
            apply ZMap.find_2 in F.
            destruct (Z.eq_dec k addr2) as [KE|KNE].
            ++
              subst addr2.
              specialize (MIcap k).
              pose proof (MapsTo_fun F H) as E.
              subst p.
              clear H.
              specialize (MIcap g F bs).
              auto.
            ++
              specialize (MIcap k g H bs H0).
              destruct MIcap as [M1 [c [M2 [a [alloc_id [M3 M4]]]]]].
              split;[assumption|].
              exists c.
              split.
              assumption.
              exists a, alloc_id.
              split.
              assumption.
              assumption.
  Qed.

  Instance memcpy_copy_data_PreservesInvariant
    (loc: location_ocaml)
    (ptrval1 ptrval2: pointer_value)
    (index: nat)
    :
    forall s, PreservesInvariant mem_invariant s (memcpy_copy_data loc ptrval1 ptrval2 index).
  Proof.
    intros s.
    unfold memcpy_copy_data.
    revert ptrval1 ptrval2 s.
    induction index; intros.
    + preserves_step.
    +
      preserves_steps.
      all: try typeclasses eauto.
  Qed.


  Instance memcpy_args_check_SameState
    (loc:location_ocaml)
    (p1 p2: pointer_value_indt)
    (n:Z ):
    SameState (memcpy_args_check loc p1 p2 n).
  Proof.
    unfold memcpy_args_check.
    same_state_steps.
  Qed.

  Fact find_cap_allocation_st_spec
    (s : mem_state_r)
    (c : Capability_GS.t)
    (sid : storage_instance_id)
    (a : allocation)
    :
    find_cap_allocation_st s c = Some (sid, a) ->
    ZMap.find (elt:=allocation) sid (allocations s) = Some a.
  Proof.
    intros H.
    unfold find_cap_allocation_st in H.
    break_let.
    apply zmap_find_first_exists in H.
    assumption.
  Qed.

  Fact eff_array_shift_ptrval_uchar_spec
    (loc : location_ocaml)
    (p : provenance)
    (c : Capability_GS.t)
    (n : Z)
    (s: mem_state)
    :
          forall v,
            eff_array_shift_ptrval loc (PV p (PVconcrete c)) CoqCtype.unsigned_char (IV n) s =  (s, inr v) ->
            v =
              (PV p
                 (PVconcrete
                    (Capability_GS.cap_set_value c
                       (AddressValue.of_Z
                          (cap_to_Z c + n)
                       )
              ))).
  Proof.
    intros ptrval H.
    Transparent serr2InternalErr bind raise ret get fail fail_noloc.
    unfold eff_array_shift_ptrval, serr2InternalErr, option2serr, raise, bind, ret, Exception_serr, Exception_errS, Exception_either, memM_monad, Monad_errS, Monad_either in H.
    unfold PNVI_prov in *.
    repeat rewrite resolve_has_PNVI in H.
    cbn in H.
    rewrite MorelloImpl.uchar_size in H.
    unfold fail_noloc in H.
    cbn in H.
    Opaque serr2InternalErr bind raise ret get fail fail_noloc.
    repeat break_let.
    cbn in H.
    repeat break_match_hyp;
      repeat break_let; repeat tuple_inversion; try rewrite Z.mul_1_l; reflexivity.
  Qed.

  Lemma load_uchar_spec
    {loc : location_ocaml}
    (p : provenance)
    {c : Capability_GS.t}
    {s : mem_state_r}
    {f : footprint}
    {mval : mem_value}:

    load loc CoqCtype.unsigned_char (PV p (PVconcrete c)) s = (s, inr (f, mval)) ->
    (
      mval = MVunspecified CoqCtype.unsigned_char
      \/
        exists ab b bv,
          ZMap.MapsTo (AddressValue.to_Z (Capability_GS.cap_get_value c)) ab (bytemap s)
          /\ mval = MVinteger (CoqIntegerType.Unsigned CoqIntegerType.Ichar) (IV b)
          /\ value ab = Some bv
          /\ byte_of_Z b = bv
    ).
  Proof.
    intros H.

    unfold load in H.
    unfold break_PV in H.
    rewrite resolve_has_PNVI in H.
    repeat rewrite resolve_has_any_PNVI_flavour in H.
    destruct p.
    -
      unfold sizeof in H.
      cbn in H.
      rewrite MorelloImpl.uchar_size in H.
      cbn in H.

      Opaque extract_unspec split_bytes.
      state_inv_step; try rewrite Znat.Nat2Z.inj_0 in *;
        try rewrite Z.add_0_r in *;
        try lia; try break_match_hyp; try discriminate; auto.
      Transparent extract_unspec split_bytes.
      +
        (* SW_strict_reads = true
         ZMap.find (elt:=AbsByte) (cap_to_Z c) (bytemap st) = Some _
         *)
        apply ZMap.find_2 in Heqo0.
        cbn in H15.
        inl_inr_inv.
        rewrite provenance_eqb_reflexivity in H1, H5.
        cbn in H1.
        break_match_hyp;
          cbn in H5;
          repeat break_match_hyp; try discriminate; subst;

            (cbn in Heqo;
             repeat break_match_hyp; try discriminate; subst;
             right;
             exists a0, zb, a1;
             repeat split; auto;
             destruct l0;
             invc Heqo;
             apply Z_of_bytes_bytes_of_Z; auto).
      +
        (* SW_strict_reads = true
         ZMap.find (elt:=AbsByte) (cap_to_Z c) (bytemap st) = None
         *)
        exfalso.
        cbn in H15.
        break_match_hyp.
        2:{
          rewrite provenance_eqb_reflexivity in Heqb1.
          inv Heqb1.
        }
        clear Heqb1 H8 H10.
        inl_inr_inv.
        destruct b; [discriminate|].
        destruct l; [discriminate|].
        inv H7.
        cbn in Heqo.
        discriminate.
      +
        (* SW_strict_reads = false
           ZMap.find (elt:=AbsByte) (cap_to_Z c) (bytemap st) = Some _
         *)
        apply ZMap.find_2 in Heqo0.
        cbn in H15.
        inl_inr_inv.
        rewrite provenance_eqb_reflexivity in H1, H5.
        cbn in H1.
        break_match_hyp;
          cbn in H5;
          repeat break_match_hyp; try discriminate; subst;

            (cbn in Heqo;
             repeat break_match_hyp; try discriminate; subst;
             right;
             exists a0, zb, a1;
             repeat split; auto;
             destruct l0;
             invc Heqo;
             apply Z_of_bytes_bytes_of_Z; auto).
      +
        (* SW_strict_reads = false
           ZMap.find (elt:=AbsByte) (cap_to_Z c) (bytemap st) = None
         *)
        exfalso.
        cbn in H15.
        break_match_hyp.
        2:{
          rewrite provenance_eqb_reflexivity in Heqb1.
          inv Heqb1.
        }
        clear Heqb1 H8 H10.
        inl_inr_inv.
        destruct b; [discriminate|].
        destruct l; [discriminate|].
        inv H7.
        cbn in Heqo.
        discriminate.
    -
      apply fail_inr_inv in H; tauto.
    -
      apply raise_inr_inv in H ; tauto.
  Qed.

  Lemma memcpy_copy_data_spec
    {loc:location_ocaml}
    {s s': mem_state_r}
    {ptrval1 ptrval2 ptrval1': pointer_value}
    {len: Z}
    :
    mempcpy_args_sane ptrval1 ptrval2 len ->
    memcpy_copy_data loc ptrval1 ptrval2 (Z.to_nat len) s = (s', inr ptrval1')
    ->
      forall p1 p2 c1 c2 a1 a2,
        ptrval1 = PV p1 (PVconcrete c1) ->
        ptrval2 = PV p2 (PVconcrete c2) ->
        a1 = AddressValue.to_Z (Capability_GS.cap_get_value c1) ->
        a2 = AddressValue.to_Z (Capability_GS.cap_get_value c2) ->
        fetch_bytes (bytemap s') a1 (Z.to_nat len) = fetch_bytes (bytemap s') a2 (Z.to_nat len).
  Proof.
    intros H H0 p1 p2 c1 c2 a1 a2 H1 H2 H3 H4.
    unfold fetch_bytes.
    apply list.list_eq_Forall2.
    eapply Forall2_nth_list.
    -
      rewrite 2!map_length.
      subst.
      rewrite 2!list_init_len.
      reflexivity.
    -
      rewrite map_length.
      intros i H5.
      rewrite 2!map_nth with (d:=0).
      rewrite list_init_len in H5.

      pose proof (list_init_nth _ (fun i : nat => a1 + Z.of_nat i) _ H5) as LI1.
      eapply nth_error_nth in LI1.
      erewrite LI1.
      clear LI1.

      pose proof (list_init_nth _ (fun i : nat => a2 + Z.of_nat i) _ H5) as LI2.
      eapply nth_error_nth in LI2.
      erewrite LI2.
      clear LI2.

      unfold PNVI_prov.
      rewrite resolve_has_PNVI.

      remember (Z.to_nat len) as n eqn:N.
      replace len with (Z.of_nat n) in H by lia.
      clear N len.
      revert i H5 H H0.
      revert s s'.
      induction n;intros.
      +
        inversion H5.
      +
        destruct (Nat.eq_dec i n) as [E|NE].
        *
          clear IHn.
          subst i.
          cbn in H0.
          state_inv_step.
          apply eff_array_shift_ptrval_uchar_spec in H0.
          apply eff_array_shift_ptrval_uchar_spec in H6.
          subst ptrval2'.
          apply load_uchar_spec in H2.

          (* TODO:
             2. need 'store_spec' for 1 byte
           *)
          admit.
        *
          cbn in H0.

          state_inv_step.
          specialize (IHn s0 s').
          apply IHn; clear IHn.
          lia.
          --
            invc H.
            econstructor; eauto.
            lia.
            lia.
          --
            assumption.
  Admitted.


  Lemma memcpy_arg_sane_after_check
    (ptrval1 ptrval2 : pointer_value)
    (s s' : mem_state_r)
    (loc : location_ocaml)
    (n : Z):
      memcpy_args_check loc ptrval1 ptrval2 n s = (s', inr tt) -> mempcpy_args_sane ptrval1 ptrval2 n.
  Proof.
    intros H.
    unfold memcpy_args_check in H.
    Transparent raise ret fail.
    unfold fail, raise, ret, Monad_either, Exception_either, Exception_errS, memM_monad, Monad_errS in H.
    cbn in H.
    repeat break_match; try tuple_inversion; try inl_inr.
    econstructor;eauto.
    lia.
    apply Values.Z_geb_ge in Heqb0.
    unfold cap_to_Z in Heqb0.
    lia.
  Qed.

  Instance memcpy_PreservesInvariant
    (ptrval1 ptrval2: pointer_value)
    (size_int: integer_value)
    :
    forall s, PreservesInvariant mem_invariant s (memcpy ptrval1 ptrval2 size_int).
  Proof.
    intros s.
    unfold memcpy.
    remember (Loc_other "memcpy") as loc eqn:L.

    remember (num_of_int size_int) as size.
    clear size_int Heqsize.
    break_let.

    apply bind_PreservesInvariant_value.
    intros M s' x AC.
    pose proof (memcpy_args_check_SameState loc ptrval1 ptrval2 size) as SA.
    specialize (SA _ _ _ AC).
    subst s'.
    split;[assumption|].

    destruct x.
    apply memcpy_arg_sane_after_check in AC.

    apply bind_PreservesInvariant_value.
    split.
    -
      pose proof (memcpy_copy_data_PreservesInvariant loc ptrval1 ptrval2 (Z.to_nat size) s M) as P.
      unfold post_exec_invariant, lift_sum_p,execErrS in P.
      rewrite H0 in P.
      break_match_hyp.
      inl_inr.
      inl_inr_inv.
      assumption.
    -
      pose proof (memcpy_copy_data_spec AC H0) as DS.
      clear H0 x.
      invc AC.
      remember (AddressValue.to_Z (Capability_GS.cap_get_value c1)) as a1 eqn:A1.
      remember (AddressValue.to_Z (Capability_GS.cap_get_value c2)) as a2 eqn:A2.
      specialize (DS p1 p2 c1 c2 a1 a2).
      autospecialize DS; [reflexivity|].
      autospecialize DS; [reflexivity|].
      specialize (DS A1 A2).
      remember (Z.to_nat (z * Z.of_nat (sizeof_pointer MorelloImpl.get))) as n.
      clear s H M.
      unfold memcpy_copy_tags.
      induction n; intros.
      + preserves_step.
      +
        (* !!! TODO:  rewrite [memcpy_copy_tags] similar to [ghost_tags] *)
        apply bind_PreservesInvariant_value_SameState.
        same_state_steps.
        intros M ptrval1' SH1.
        apply bind_PreservesInvariant_value_SameState.
        same_state_steps.
        intros _ ptrval2' SH2.
        preserves_step. (* _ <- ... *)
        apply bind_PreservesInvariant_value_SameState.
        same_state_steps.
        intros _ dst_a H4.
        remember (Loc_other "memcpy") as loc.

        apply eff_array_shift_ptrval_uchar_spec in SH1; subst ptrval1'.
        apply eff_array_shift_ptrval_uchar_spec in SH2; subst ptrval2'.

        Transparent serr2InternalErr bind raise ret get fail fail_noloc.
        unfold serr2InternalErr, option2serr, raise, bind, ret, Exception_serr, Exception_errS, Exception_either, memM_monad, Monad_errS, Monad_either in H4.
        Opaque serr2InternalErr bind raise ret get fail fail_noloc.
        tuple_inversion.

        apply bind_PreservesInvariant_value_SameState.
        same_state_steps.
        intros _ src_a H4.

        Transparent serr2InternalErr bind raise ret get fail fail_noloc.
        unfold serr2InternalErr, option2serr, raise, bind, ret, Exception_serr, Exception_errS, Exception_either, memM_monad, Monad_errS, Monad_either in H4.
        Opaque serr2InternalErr bind raise ret get fail fail_noloc.
        tuple_inversion.

        preserves_steps.
        all: try assumption.
        apply negb_false_iff in Heqb.
        Fail eapply (memcpy_PreservesInvariant_fact Heqo Heqb DS).
        admit.
        (* TODO *)
        Fail eapply IHn.
  Admitted.

  Instance realloc_PreservesInvariant
    (loc : location_ocaml)
    (tid : MemCommonExe.thread_id)
    (align : integer_value)
    (ptr : pointer_value)
    (size : integer_value)
    :
    forall s, PreservesInvariant mem_invariant s (realloc loc tid align ptr size).
  Proof.
    intros s.
    unfold realloc.
    rewrite resolve_has_CORNUCOPIA.
    preserves_steps. (* TODO: figure out why typeclass resolution is not happening *)
    all: try typeclasses eauto.
  Qed.

  (*

TODO: review: wrt [cap_of_mem_value] -> [resolve_function_pointer] logic
call_intrinsic
intrinsic_offset_get loc args
intrinsic_address_get loc args
intrinsic_base_get loc args
intrinsic_length_get loc args
intrinsic_tag_get loc args
intrinsic_tag_clear loc args
intrinsic_is_equal_exact loc args
intrinsic_representable_length loc args
intrinsic_representable_alignment_mask loc args
intrinsic_revoke loc
intrinsic_bounds_set loc args
intrinsic_strfcap loc args
intrinsic_perms_and loc args

Preserve:
realloc

Misc:
va_*

     *)


  End CheriMemoryWithoutPNVI.

  (* This is CHERI memory model whout instant revocation but with PNVI. *)
  Module CheriMemoryWithPNVI.
    Include CheriMemoryImplWithProofsExe(WithPNVISwitches).

    Opaque bind raise ret get put ErrorWithState.update fail fail_noloc serr2InternalErr liftM.
    Ltac preserves_step
      :=
      match goal with
      |[|- PreservesInvariant _ _ (bind get _)] => apply bind_get_PreservesInvariant
      |[|- PreservesInvariant _ _ (bind _ _)] => apply bind_PreservesInvariant
      |[|- PreservesInvariant _ _ (raise _)] => apply raise_PreservesInvariant
      |[|- PreservesInvariant _ _ (ret _)] => apply ret_PreservesInvariant
      |[|- PreservesInvariant _ _ get] => apply get_PreservesInvariant
      |[|- PreservesInvariant _ _ (put _) ] => apply put_PreservesInvariant
      |[|- PreservesInvariant _ _ (ErrorWithState.update _)] => apply update_PreservesInvariant
      |[|- PreservesInvariant _ _ (fail _ _)] => apply fail_PreservesInvariant
      |[|- PreservesInvariant _ _ (fail_noloc _)] => apply fail_noloc_PreservesInvariant
      |[|- PreservesInvariant _ _ (serr2InternalErr _)] => apply serr2InternalErr_PreservesInvariant
      |[|- PreservesInvariant _ _ (liftM _ _)] => apply liftM_PreservesInvariant
      |[|- PreservesInvariant _ _] => typeclasses eauto
      end; intros.

    Ltac preserves_steps :=
      repeat (match goal with
              | |- PreservesInvariant _ _ (match _ with _ => _ end) => break_match_goal
              | |- PreservesInvariant _ _ _ => preserves_step
              | |- context [match _ with _ => _ end] => break_match_goal
              | |- context [if _ then _ else _] => break_match_goal
              end; cbn).

    (* CheriMemoryWithPNVI memory invariant.

     In general we do not enforce where tagged caps are pointing. They
     could be pointing to live, dead, or outside of any allocation.

     However if they are pointing to an allocation the cap bounds must
     be within allocation footprint.
     *)
    Definition mem_invariant (m: mem_state_r) : Prop
      :=
      let cm := m.(capmeta) in
      let bm := m.(bytemap) in
      let am := m.(allocations) in

      base_mem_invariant m
      /\
        (* All caps which are tagged according to capmeta must: *)
        (forall addr g,
            ZMap.MapsTo addr (true,g) cm ->
            (forall bs, fetch_bytes bm addr (sizeof_pointer MorelloImpl.get) = bs ->
                   (
                     (* Have the same provenance and correct sequence bytes *)
                     (exists p,
                         split_bytes_ptr_spec p bs
                         (* decode without error *)
                         /\ (exists c, decode_cap bs true c
                                 (* if there is a live allocation, *)
                                 /\ (forall alloc_id,
                                       (* if pointer has concerete provenance *)
                                       p = Prov_some alloc_id ->
                                       (* if corresponding allocation exists *)
                                       (forall a, ZMap.MapsTo alloc_id a am ->
                                             (* the cap bounds must within it *)
                                             cap_bounds_within_alloc c a)
                                   )
                           )
                     )
                   )
            )
        ).

    Lemma resolve_has_PNVI:
      has_PNVI (WithPNVISwitches.get_switches tt) = true.
    Proof.
      unfold WithPNVISwitches.get_switches.
      generalize (remove_Revocation (remove_PNVI (abst_get_switches tt))) as s.
      intros s.
      unfold has_PNVI in *.
      apply existsb_exists.
      exists (SW_PNVI AE_UDI).
      split.
      -
        apply set_add_iff.
        left.
        reflexivity.
      -
        reflexivity.
    Qed.

    Lemma resolve_has_INSTANT:
      has_switch (WithPNVISwitches.get_switches tt) (SW_revocation INSTANT) = false.
    Proof.
      unfold WithPNVISwitches.get_switches.
      generalize (remove_PNVI (abst_get_switches tt)) as l.
      intros l.
      unfold has_PNVI, remove_PNVI, remove_Revocation in *.
      apply Bool.not_true_is_false.
      intros E.
      apply set_mem_correct1 in E.
      apply set_add_elim2 in E.
      2:auto.
      unfold set_In in E.
      apply filter_In in E.
      destruct E as [_ E2].
      cbn in E2.
      discriminate.
    Qed.

    Lemma resolve_has_CORNUCOPIA:
      has_switch (WithPNVISwitches.get_switches tt) (SW_revocation CORNUCOPIA) = false.
    Proof.
      unfold WithPNVISwitches.get_switches.
      generalize (remove_PNVI (abst_get_switches tt)) as l.
      intros l.
      unfold has_switch.
      apply set_mem_complete2.
      intros E.
      apply set_add_elim in E.
      destruct E;[discriminate|].
      unfold remove_Revocation in H.
      apply filter_In in H.
      destruct H as [_ H].
      apply Bool.negb_true_iff in H.
      inv H.
    Qed.

    Lemma initial_mem_state_invariant:
      mem_invariant initial_mem_state.
    Proof.
      unfold initial_mem_state, mem_invariant.
      split.
      -
        (* base invariant *)
        repeat split; cbn in *.
        +
          intros alloc_id a H.
          apply empty_mapsto_iff in H;
            contradiction.
        +
          intros alloc_id1 alloc_id2 a1 a2 H H0 H1.
          apply empty_mapsto_iff in H0;
            contradiction.
        +
          unfold zmap_forall_keys.
          intros k H.
          apply empty_in_iff in H;
            contradiction.
        +
          unfold zmap_forall_keys.
          intros k H.
          apply empty_in_iff in H.
          tauto.
        +
          unfold zmap_forall.
          intros k v H.
          apply empty_mapsto_iff in H.
          tauto.
      -
          intros addr g H bs H0.
          apply empty_mapsto_iff in H;
            contradiction.
    Qed.

    (* this lemma is exactly same as non-PNVI but I do not see how to re-use the proof,
       as they are using different formulations of the [mem_invariant].
     *)
    Lemma mem_state_after_ghost_tags_preserves:
      forall m addr size,
        mem_invariant m ->
        mem_invariant (mem_state_with_capmeta
                         (init_ghost_tags addr size (capmeta m))
                         m).
    Proof.
      intros m addr sz H.
      destruct H as [MIbase MIcap].
      destruct_base_mem_invariant MIbase.
      split.
      -
        (* base invariant *)
        clear MIcap.
        repeat split;auto.
        repeat split;auto.

        (* alignment proof *)
        intros a E.
        apply zmap_in_mapsto in E.
        destruct E as [tg E].
        unfold mem_state_with_capmeta in E.
        simpl in E.
        apply init_ghost_tags_spec in E.
        destruct E.
        +
          (* capmeta unchanged at [a] *)
          apply zmap_mapsto_in in H.
          apply Balign.
          apply H.
        +
          (* capmeta cleared *)
          destruct H as [H1 H2].
          apply H1.
      -
        intros a g E bs F.
        simpl in *.
        apply init_ghost_tags_spec in E.
        destruct E as [E | [A E]].
        +
          (* capmeta unchanged at [a] *)
          specialize (MIcap a g E bs F).
          apply MIcap.
        +
          inversion E.
    Qed.

    (* TODO: move *)
    Lemma AddressValue_of_Z_to_Z:
      forall x, AddressValue.of_Z  (AddressValue.to_Z x) = x.
    Proof.
      intros x.
      unfold AddressValue.of_Z, AddressValue.to_Z.
      unfold bv_to_Z_unsigned.
      apply bitvector.Z_to_bv_bv_unsigned.
    Qed.

    Instance allocator_PreservesInvariant
      (size: nat)
      (align: Z)
      (is_dynamic: bool)
      (pref: CoqSymbol.prefix)
      (ty: option CoqCtype.ctype)
      (ro_status: readonly_status)
      :
      forall s,
        PreservesInvariant mem_invariant s (allocator size align is_dynamic pref ty ro_status).
    Proof.
      intros s.
      unfold allocator.
      apply bind_PreservesInvariant_value_SameState;[same_state_step|].
      intros I m H.
      Transparent get.
      unfold get, State_errS in H.
      Opaque get.
      tuple_inversion.
      break_let.
      break_if;[preserves_step|].
      preserves_step;[|preserves_step].
      preserves_step.
      remember (AddressValue.of_Z
             (AddressValue.to_Z (last_address m) - Z.of_nat size -
              (if z <? 0 then - z0 else z0))) as addr.
      pose proof (mem_state_after_ghost_tags_preserves m addr size I).
      destruct I as [Ibase I].
      destruct_base_mem_invariant Ibase.
      destruct m.
      cbn in *.
      split.
      -
        (* base *)
        clear I.
        repeat split;cbn.
        +
          (* dead *)
          intros alloc_id a H1.
          destruct (Z.eq_dec next_alloc_id0 alloc_id ) as [E|NE].
          *
            apply add_mapsto_iff in H1.
            destruct H1 as [[H2 H3] | H4].
            --
              subst a.
              auto.
            --
              lia.
          *
            apply (ZMap.add_3 NE) in H1.
            apply (Bdead _ _ H1).
        +
          (* no-overlap *)
          intros alloc_id1 alloc_id2 a1 a2 NA M1 M2.
          admit.
        +
          (* align *)
          intros addr'.
          apply H.
        +
          (* Bnextallocid *)
          clear H.
          intros alloc_id.
          destruct (Z.eq_dec next_alloc_id0 alloc_id ) as [E|NE].
          *
            lia.
          *
            intros H.
            apply add_neq_in_iff in H;auto.
            specialize (Bnextallocid alloc_id H).
            cbn in Bnextallocid.
            lia.
        +
          (* Blastaddr *)
          clear Bdead Bnooverlap Bnextallocid H.
          intros alloc_id a.
          intros H.
          destruct (Z.eq_dec next_alloc_id0 alloc_id ) as [E|NE].
          *
            apply add_mapsto_iff in H.
            destruct H as [[H2 H3] | H4].
            --
              subst a.
              cbn.
              lia.
            --
              lia.
          *
            apply (ZMap.add_3 NE) in H.
            specialize (Blastaddr alloc_id a H). clear H.
            cbn in Blastaddr.

            (* need some relation between [addr] and [last_address0] *)

            admit.
      -
        (* mem_invariant *)
        admit.
    Admitted.
    Opaque allocator.

    Instance  remove_allocation_PreservesInvariant
      (alloc_id : CheriMemoryTypesExe.storage_instance_id)
      (s : mem_state_r):
      PreservesInvariant mem_invariant s (remove_allocation alloc_id).
    Proof.
      unfold remove_allocation.
      preserves_step.
      destruct H as [Hbase Hcap].
      (* destruct_base_mem_invariant Sbase. *)
      split;cbn.
      -
        (* base *)
        clear Hcap.
        destruct_base_mem_invariant Hbase.
        repeat split; cbn.
        +
          intros alloc_id0 a H.
          apply ZMap.remove_3 in H.
          eapply Bdead;eauto.
        +
          intros alloc_id1 alloc_id2 a1 a2 N H H0.
          apply ZMap.remove_3 in H0, H.
          eapply Bnooverlap.
          eauto.
          eauto.
          eauto.
        +
          apply Balign.
        +
          apply zmap_forall_keys_remove, Bnextallocid.
        +
          apply zmap_forall_remove, Blastaddr.
      -
        clear Hbase.
        intros addr g A bs F.
        specialize (Hcap addr g A bs F).
        destruct Hcap as [p [H1 [c [H2 H3]]]].
        exists p. split;[assumption|].
        exists c. split;[assumption|].
        intros alloc_id' P a M.
        destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
        +
          (* [alloc_id] is being removed *)
          exfalso.
          subst alloc_id'.
          apply remove_mapsto_iff in M.
          destruct M as [M _].
          congruence.
        +
          apply remove_neq_mapsto_iff in M;[|assumption].
          eapply H3;eauto.
    Qed.

    Instance kill_PreservesInvariant
      (loc : location_ocaml)
      (is_dyn : bool)
      (ptr : pointer_value_indt)
      :
      forall s,
        PreservesInvariant mem_invariant s (kill loc is_dyn ptr).
    Proof.
      unfold kill.
      rewrite resolve_has_PNVI, resolve_has_INSTANT, resolve_has_CORNUCOPIA.
      destruct ptr.
      destruct p eqn:P; intros.
      1,2: preserves_steps.
      break_match_goal; [preserves_step|cbn].
      break_match_goal; [preserves_step|].
      apply bind_PreservesInvariant_value.
      intros H s' x H0.
      pose proof (get_allocation_opt_SameState s) as H2.
      specialize (H2 _ _ _ H0).
      subst s'.
      split;[assumption|].
      preserves_steps.
      - typeclasses eauto.
    Qed.

  End CheriMemoryWithPNVI.

(* Equivalence proofs below are temporary commented out


  (*
    Pointer equality. The first pointer is from the "WithPNVI" memory
    model, while the second one is from the "WithoutPNVI".

    Despite being the same type [pointer_value_indt], the relation is
    non-symmetric, non-transitive, and irreflexive!

    RHS provenance could only be [Prov_disabled].
 *)
  Inductive ptr_value_same
    (m1: CheriMemoryWithPNVI.mem_state_r)
    (m2: CheriMemoryWithoutPNVI.mem_state_r): relation pointer_value_indt
    :=

  (* -- stateless cases -- *)

  | ptr_value_same_none: forall b1 b2,  b1 = b2 -> ptr_value_same m1 m2 (PV Prov_none b1) (PV Prov_disabled b2)
  | ptr_value_same_device: forall b1 b2,  b1 = b2 -> ptr_value_same m1 m2 (PV Prov_device b1) (PV Prov_disabled b2)
  (* function pointers are not revoked *)
  | ptr_value_same_some_func: forall f1 f2 pr1,
      f1 = f2
      -> ptr_value_same m1 m2 (PV pr1 (PVfunction f1)) (PV Prov_disabled (PVfunction f2))

  (* -- stateful cases -- *)

  | ptr_value_same_some_conc: forall c1 c2 alloc_id,
      single_alloc_id_cap_cmp m1.(CheriMemoryWithPNVI.allocations) alloc_id c1 c2  ->
      ptr_value_same m1 m2 (PV (Prov_some alloc_id) (PVconcrete c1)) (PV Prov_disabled (PVconcrete c2)).

  (* The following prevent default elimination principle from being generated for
     this type, as it is inadequate *)
  Unset Elimination Schemes.
  (* This relation is non-reflexive (but not irreflexive) *)
  Inductive mem_value_with_err_same: CheriMemoryWithPNVI.mem_state_r -> CheriMemoryWithoutPNVI.mem_state_r -> mem_value_with_err -> mem_value_with_err -> Prop
    :=
  | mem_value_with_err_same_MVEunspecified: forall m1 m2 t1 t2, t1 = t2 -> mem_value_with_err_same m1 m2 (MVEunspecified t1) (MVEunspecified t2)
  | mem_value_with_err_same_MVEinteger: forall m1 m2 t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_with_err_same m1 m2 (MVEinteger t1 v1) (MVEinteger t2 v2)
  | mem_value_with_err_same_MVEfloating: forall m1 m2 t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_with_err_same m1 m2 (MVEfloating t1 v1) (MVEfloating t2 v2)
  | mem_value_with_err_same_MVEpointer: forall m1 m2 t1 t2 p1 p2, t1 = t2 /\ ptr_value_same m1 m2 p1 p2 -> mem_value_with_err_same m1 m2 (MVEpointer t1 p1) (MVEpointer t2 p2)
  | mem_value_with_err_same_MVEarray: forall m1 m2 a1 a2, eqlistA (mem_value_with_err_same m1 m2) a1 a2 -> mem_value_with_err_same m1 m2 (MVEarray a1) (MVEarray a2)
  | mem_value_with_err_same_MVErr: forall m1 m2 e1 e2, e1 = e2 -> mem_value_with_err_same m1 m2 (MVErr e1) (MVErr e2)
  | mem_value_with_err_same_MVEstruct: forall m1 m2 tag_sym1 l1 tag_sym2 l2,
      tag_sym1 = tag_sym2  ->
      eqlistA (struct_with_err_field_eq m1 m2) l1 l2 ->
      mem_value_with_err_same m1 m2 (MVEstruct tag_sym1 l1) (MVEstruct tag_sym2 l2)
  | mem_value_with_err_same_MVEunion: forall m1 m2 tag_sym1 id1 v1 tag_sym2 id2 v2,
      tag_sym1 = tag_sym2 /\ id1 = id2 /\ mem_value_with_err_same m1 m2 v1 v2 ->
      mem_value_with_err_same m1 m2 (MVEunion tag_sym1 id1 v1) (MVEunion tag_sym2 id2 v2)
  with
    struct_with_err_field_eq: CheriMemoryWithPNVI.mem_state_r -> CheriMemoryWithoutPNVI.mem_state_r ->
                              (CoqSymbol.identifier * CoqCtype.ctype * mem_value_with_err) -> (CoqSymbol.identifier * CoqCtype.ctype * mem_value_with_err) -> Prop :=
  | struct_field_with_err_triple_eq: forall m1 m2 id1 id2 t1 t2 v1 v2,
      id1 = id2 /\ t1 = t2 /\ mem_value_with_err_same m1 m2 v1 v2 -> struct_with_err_field_eq m1 m2 (id1,t1,v1) (id2,t2,v2).
  Set Elimination Schemes.

  (* Custom induction principle for mem_value_with_err_same *)
  Lemma mem_value_with_err_same_ind:
    forall (m1 : CheriMemoryWithPNVI.mem_state_r) (m2 : CheriMemoryWithoutPNVI.mem_state_r)
           (P : mem_value_with_err -> mem_value_with_err -> Prop),

      (forall t1 t2, t1 = t2 -> P (MVEunspecified t1) (MVEunspecified t2)) ->
      (forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> P (MVEinteger t1 v1) (MVEinteger t2 v2)) ->
      (forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> P (MVEfloating t1 v1) (MVEfloating t2 v2)) ->
      (forall t1 t2 p1 p2, t1 = t2 /\ ptr_value_same m1 m2 p1 p2 -> P (MVEpointer t1 p1) (MVEpointer t2 p2)) ->
      (forall e1 e2, e1 = e2 -> P (MVErr e1) (MVErr e2)) ->

      (forall a1 a2, eqlistA (mem_value_with_err_same m1 m2) a1 a2 -> List.Forall2 P a1 a2 -> P (MVEarray a1) (MVEarray a2)) ->
      (forall tag_sym1 l1 tag_sym2 l2,
          tag_sym1 = tag_sym2 ->
          eqlistA (struct_with_err_field_eq m1 m2) l1 l2 ->
          List.Forall2 (fun '(id1, ct1, mv1) '(id2, ct2, mv2) => id1 = id2 /\ ct1 = ct2 /\ P mv1 mv2) l1 l2 ->
          P (MVEstruct tag_sym1 l1) (MVEstruct tag_sym2 l2)) ->

      (forall tag_sym1 id1 v1 tag_sym2 id2 v2,
          tag_sym1 = tag_sym2 /\ id1 = id2 /\ mem_value_with_err_same m1 m2 v1 v2 ->
          P v1 v2 ->
          P (MVEunion tag_sym1 id1 v1) (MVEunion tag_sym2 id2 v2)) ->

      forall x y, mem_value_with_err_same m1 m2 x y -> P x y.
  Proof.
    intros m1 m2 P Hbase_unspecified Hbase_integer Hbase_floating Hbase_pointer Hbase_err
      Hrec_array Hrec_struct Hrec_union.
    fix IH 3.
    intros x y H.
    destruct x, y; inversion H; subst; clear H.

    - apply Hbase_unspecified. reflexivity.
    - apply Hbase_integer. assumption.
    - apply Hbase_floating. assumption.
    - apply Hbase_pointer. assumption.
    - apply Hbase_err. reflexivity.

    - apply Hrec_array; [assumption|].
      clear Hrec_array.
      induction H4.
      + constructor.
      + constructor; [apply IH; assumption | apply IHeqlistA; assumption].

    - apply Hrec_struct; [reflexivity | assumption |].
      clear Hrec_struct.
      induction H7.
      + constructor.
      + inversion H; subst; clear H.
        destruct H0 as [H1 [H2 H3]].
        subst.
        constructor.
        split;auto.
        apply IHeqlistA.
    - destruct H3 as [H4 [H5 H6]].
      apply Hrec_union.
      split;auto.
      apply IH.
      auto.
  Qed.


  (* The following prevent default elimination principle from being generated for
     this type, as it is inadequate *)
  Unset Elimination Schemes.
  (* This relation is non-reflexive *)
  Inductive mem_value_indt_same: CheriMemoryWithPNVI.mem_state_r -> CheriMemoryWithoutPNVI.mem_state_r -> mem_value_indt -> mem_value_indt -> Prop
    :=
  | mem_value_indt_same_MVunspecified: forall m1 m2 t1 t2, t1 = t2 -> mem_value_indt_same m1 m2 (MVunspecified t1) (MVunspecified t2)
  | mem_value_indt_same_MVinteger: forall m1 m2 t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_indt_same m1 m2 (MVinteger t1 v1) (MVinteger t2 v2)
  | mem_value_indt_same_MVfloating: forall m1 m2 t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_indt_same m1 m2 (MVfloating t1 v1) (MVfloating t2 v2)
  | mem_value_indt_same_MVpointer: forall m1 m2 t1 t2 p1 p2, t1 = t2 /\ ptr_value_same m1 m2 p1 p2 -> mem_value_indt_same m1 m2 (MVpointer t1 p1) (MVpointer t2 p2)
  | mem_value_indt_same_MVarray: forall m1 m2 a1 a2, eqlistA (mem_value_indt_same m1 m2) a1 a2 -> mem_value_indt_same m1 m2 (MVarray a1) (MVarray a2)
  | mem_value_indt_same_MVstruct: forall m1 m2 tag_sym1 l1 tag_sym2 l2,
      tag_sym1 = tag_sym2 ->
      eqlistA (struct_field_eq m1 m2) l1 l2 ->
      mem_value_indt_same m1 m2 (MVstruct tag_sym1 l1) (MVstruct tag_sym2 l2)
  | mem_value_indt_same_MVunion: forall m1 m2 tag_sym1 id1 v1 tag_sym2 id2 v2,
      tag_sym1 = tag_sym2 /\ id1 = id2 /\ mem_value_indt_same m1 m2 v1 v2 ->
      mem_value_indt_same m1 m2 (MVunion tag_sym1 id1 v1) (MVunion tag_sym2 id2 v2)
  with
    struct_field_eq: CheriMemoryWithPNVI.mem_state_r -> CheriMemoryWithoutPNVI.mem_state_r -> (CoqSymbol.identifier * CoqCtype.ctype * mem_value_indt) -> (CoqSymbol.identifier * CoqCtype.ctype * mem_value_indt) -> Prop
    :=
  | struct_field_triple_eq: forall m1 m2 id1 id2 t1 t2 v1 v2,
      id1 = id2 /\ t1 = t2 /\ mem_value_indt_same m1 m2 v1 v2 -> struct_field_eq m1 m2 (id1,t1,v1) (id2,t2,v2).
  Set Elimination Schemes.

  (* Custom induction principle for mem_value_indt_same *)
  Lemma mem_value_indt_same_ind:
    forall (m1 : CheriMemoryWithPNVI.mem_state_r) (m2 : CheriMemoryWithoutPNVI.mem_state_r)
           (P : mem_value_indt -> mem_value_indt -> Prop),

      (forall t1 t2, t1 = t2 -> P (MVunspecified t1) (MVunspecified t2)) ->
      (forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> P (MVinteger t1 v1) (MVinteger t2 v2)) ->
      (forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> P (MVfloating t1 v1) (MVfloating t2 v2)) ->
      (forall t1 t2 p1 p2, t1 = t2 /\ ptr_value_same m1 m2 p1 p2 -> P (MVpointer t1 p1) (MVpointer t2 p2)) ->

      (forall a1 a2, eqlistA (mem_value_indt_same m1 m2) a1 a2 -> List.Forall2 P a1 a2 -> P (MVarray a1) (MVarray a2)) ->
      (forall tag_sym1 l1 tag_sym2 l2,
          tag_sym1 = tag_sym2 ->
          eqlistA (struct_field_eq m1 m2) l1 l2 ->
          List.Forall2 (fun '(id1, _, mv1) '(id2, _, mv2) => id1 = id2 /\ P mv1 mv2) l1 l2 ->
          P (MVstruct tag_sym1 l1) (MVstruct tag_sym2 l2)) ->

      (forall tag_sym1 id1 v1 tag_sym2 id2 v2,
          tag_sym1 = tag_sym2 /\ id1 = id2 /\ mem_value_indt_same m1 m2 v1 v2 ->
          P v1 v2 ->
          P (MVunion tag_sym1 id1 v1) (MVunion tag_sym2 id2 v2)) ->

      forall x y, mem_value_indt_same m1 m2 x y -> P x y.
  Proof.
    intros m1 m2 P Hbase_unspecified Hbase_integer Hbase_floating Hbase_pointer
      Hrec_array Hrec_struct Hrec_union.
    fix IH 3.
    intros x y H.
    destruct x, y; inversion H; subst; clear H.

    - apply Hbase_unspecified; auto.
    - apply Hbase_integer; auto.
    - apply Hbase_floating; auto.
    - apply Hbase_pointer; auto.

    - apply Hrec_array; auto.
      + induction H4; constructor.
        apply IH; auto.
        apply IHeqlistA; auto; apply H2.
    - apply Hrec_struct; auto.
      + clear Hrec_struct.
        induction H7; constructor.
        inversion H; subst.
        destruct H0 as [H1 [H2 H3]].
        split;auto.
        apply IHeqlistA; auto.
    - apply Hrec_union; auto.
      apply IH; auto.
      destruct H3; destruct H0; auto.
  Qed.

  Inductive ctype_pointer_value_same:
    CheriMemoryWithPNVI.mem_state_r ->
    CheriMemoryWithoutPNVI.mem_state_r ->
    (CoqCtype.ctype * pointer_value_indt) ->
    (CoqCtype.ctype * pointer_value_indt) -> Prop
    :=
  | ctype_pointer_value_same_1:
    forall m1 m2 t1 t2 pv1 pv2, t1 = t2 /\ ptr_value_same m1 m2 pv1 pv2 ->
                                ctype_pointer_value_same m1 m2 (t1,pv1) (t2,pv2).

  Inductive varargs_same:
    CheriMemoryWithPNVI.mem_state_r ->
    CheriMemoryWithoutPNVI.mem_state_r ->
    (Z * list (CoqCtype.ctype * pointer_value_indt)) ->
    (Z * list (CoqCtype.ctype * pointer_value_indt)) -> Prop
    :=
  | varargs_same_1: forall m1 m2 z1 vl1 z2 vl2,
      z1 = z2 /\ eqlistA (ctype_pointer_value_same m1 m2) vl1 vl2
      -> varargs_same m1 m2 (z1,vl1) (z2,vl2).

  (** A predicate that defines the relationship between two capmeta
      elements with key [addr] from two different capability maps
      within the memory state context provided by the [bytemap] and
      [allocatations] *)
  Inductive addr_cap_meta_same :
    CheriMemoryWithPNVI.mem_state_r ->
    CheriMemoryWithoutPNVI.mem_state_r ->
    Z -> (* addr *)
    bool * CapGhostState -> (* meta1 *)
    bool * CapGhostState -> (* meta2 *)
    Prop :=
  (* this covers non-revoked caps as well as caps pointing to device ranges *)
  | addr_cap_meta_same_tags_and_ghost_state :
    forall m1 m2 addr meta,
      addr_cap_meta_same m1 m2 addr meta meta
  (* this covers a situation when cap corresponding to [meta2] has been revoked *)
  | addr_cap_meta_same_revoked :
    forall m1 m2 addr gs1 gs2 c1 c2 bs1 bs2 prov,
      CheriMemoryWithPNVI.fetch_bytes m1.(CheriMemoryWithPNVI.bytemap) addr (sizeof_pointer MorelloImpl.get) = bs1
      -> CheriMemoryWithPNVI.fetch_bytes m2.(CheriMemoryWithoutPNVI.bytemap) addr (sizeof_pointer MorelloImpl.get) = bs2
      -> split_bytes_ptr_spec prov bs1
      -> split_bytes_ptr_spec Prov_disabled bs2
      -> decode_cap bs1 true c1 (* decoding error should never happen *)
      -> decode_cap bs2 false c2 (* decoding error should never happen *)
      -> ptr_value_same m1 m2 (PV prov (PVconcrete c1)) (PV Prov_disabled (PVconcrete c2))
      -> gs2.(tag_unspecified) = false
      -> gs1.(bounds_unspecified) = gs2.(bounds_unspecified)
      -> addr_cap_meta_same m1 m2 addr (true, gs1) (false, gs2).

  (* Prior to calling this, we have already established that the
     [allocations] fields are the same in both memory states, so we
     pass just one copy.

     Similarly, the [bytemap] fields are the same up to provenance
     information. Since the non-PNVI version is supposed to have all
     provenance fields set to `Prof_disabled`, we assume that here we
     pass the PNVI version of bytemap, which may contain additional
     provenance information.  *)
  Definition capmeta_same
    (m1:CheriMemoryWithPNVI.mem_state_r)
    (m2:CheriMemoryWithoutPNVI.mem_state_r)
    capmeta1 capmeta2
    : Prop
    :=
    zmap_relate_keys capmeta1 capmeta2 (addr_cap_meta_same m1 m2).

  (* TODO: Needs to be reviewed wrt revocation. *)
  Definition mem_state_same
    (m1:CheriMemoryWithPNVI.mem_state_r)
    (m2:CheriMemoryWithoutPNVI.mem_state_r)
    : Prop
    :=
    m1.(CheriMemoryWithPNVI.next_alloc_id) = m2.(CheriMemoryWithoutPNVI.next_alloc_id)
    /\ m1.(CheriMemoryWithPNVI.last_address) = m2.(CheriMemoryWithoutPNVI.last_address)
    /\ ZMap.Equal m1.(CheriMemoryWithPNVI.allocations) m2.(CheriMemoryWithoutPNVI.allocations)
    /\ ZMap.Equal m1.(CheriMemoryWithPNVI.funptrmap) m2.(CheriMemoryWithoutPNVI.funptrmap)
    /\ ZMap.Equiv (varargs_same m1 m2) m1.(CheriMemoryWithPNVI.varargs) m2.(CheriMemoryWithoutPNVI.varargs)
    /\ m1.(CheriMemoryWithPNVI.next_varargs_id) = m2.(CheriMemoryWithoutPNVI.next_varargs_id)
    /\ ZMap.Equiv AbsByte_eq m1.(CheriMemoryWithPNVI.bytemap) m2.(CheriMemoryWithoutPNVI.bytemap)
    /\ capmeta_same m1 m2 m1.(CheriMemoryWithPNVI.capmeta) m2.(CheriMemoryWithoutPNVI.capmeta).


  Ltac destruct_mem_state_same H
    :=
    let Malloc_id := fresh "Malloc_id" in
    let Mlastaddr := fresh "Mlastaddr" in
    let Mallocs := fresh "Mallocs" in
    let Mfuncs := fresh "Mfuncs" in
    let Mvarargs := fresh "Mvarargs" in
    let Mnextvararg := fresh "Mnextvararg" in
    let Mbytes := fresh "Mbytes" in
    let Mcapmeta := fresh "Mcapmeta" in
    destruct H as (Malloc_id & Mlastaddr & Mallocs & Mfuncs & Mvarargs & Mnextvararg & Mbytes & Mcapmeta).

  Lemma base_mem_state_same_invariants:
    forall m1 m2,
      mem_state_same m1 m2 ->
      (CheriMemoryWithPNVI.base_mem_invariant m1 <-> CheriMemoryWithoutPNVI.base_mem_invariant m2).
  Proof.
    intros m1 m2 M.
    destruct_mem_state_same M.
    split.
    -
      (* mem_invariant_WithPNVI m1 -> mem_invariant_WithoutPNVI m2 *)
      unfold CheriMemoryWithPNVI.base_mem_invariant, CheriMemoryWithoutPNVI.base_mem_invariant.
      subst.
      intros [H1 [H2 H3]].
      repeat split.
      +
        (* ... -> is_dead a = false *)
        intros alloc_id a H.
        apply (H1 alloc_id).
        rewrite Mallocs.
        assumption.
      +
        (* ... -> allocations_do_no_overlap a1 a2 *)
        intros alloc_id1 alloc_id2 a1 a2 H H0.
        eapply H2.
        eauto.
        rewrite Mallocs.
        eapply H.
        rewrite Mallocs.
        eapply H0.
      +
        (* zmap_forall_keys (fun addr : Z => addr mod alignof_pointer MorelloImpl.get = 0)  (CheriMemoryWithoutPNVI.capmeta m2) *)

        unfold capmeta_same in Mcapmeta.
        unfold zmap_forall_keys in *.
        intros k I.
        specialize (H2 k).
        apply zmap_relate_keys_same_keys with (k:=k) in Mcapmeta.
        apply H3.
        apply Mcapmeta.
        apply I.
    -
      (* not provable *)
      (* mem_invariant_WithoutPNVI m2 -> mem_invariant_WithPNVI m1  *)
      unfold CheriMemoryWithPNVI.base_mem_invariant, CheriMemoryWithoutPNVI.base_mem_invariant.
      subst.
      intros [H1 [H2 H3]].
      repeat split.
      +
        (* ... -> is_dead a = false *)
        intros alloc_id a H.
        apply (H1 alloc_id).
        rewrite <- Mallocs.
        assumption.
      +
        (* ... -> allocations_do_no_overlap a1 a2 *)
        intros alloc_id1 alloc_id2 a1 a2 H H0.
        eapply H2.
        rewrite <- Mallocs.
        eapply H.
        rewrite <- Mallocs.
        eapply H0.
      +
        (* zmap_forall_keys (fun addr : Z => addr mod alignof_pointer MorelloImpl.get = 0)  (CheriMemoryWithPNVI.capmeta m1) *)
        unfold capmeta_same in Mcapmeta.
        unfold zmap_forall_keys in *.
        intros k I.
        specialize (H2 k).
        apply zmap_relate_keys_same_keys with (k:=k) in Mcapmeta.
        apply H3.
        apply Mcapmeta.
        apply I.
  Qed.

  (* --- Helper lemmas *)

  Lemma has_PNVI_WithPNVI:
    has_PNVI (WithPNVISwitches.get_switches tt) = true.
  Proof.
    unfold WithPNVISwitches.get_switches.
    remember (abst_get_switches tt) as l.
    apply existsb_exists.
    exists (SW_PNVI AE_UDI).
    split.
    2:reflexivity.
    apply set_add_iff.
    left.
    reflexivity.
  Qed.

  Lemma remove_PNVI_In:
    forall l s,
      is_PNVI_switch s = false ->
      set_In s l <-> set_In s (remove_PNVI l).
  Proof.
    intros l s P.
    split; intros H.
    -
      unfold remove_PNVI.
      apply filter_In.
      split.
      apply H.
      apply Bool.negb_true_iff.
      assumption.
    -
      unfold remove_PNVI in H.
      apply filter_In in H.
      apply H.
  Qed.

  Lemma remove_Revocation_In:
    forall l s,
      is_Revocation_switch s = false ->
      set_In s l <-> set_In s (remove_Revocation l).
  Proof.
    intros l s P.
    split; intros H.
    -
      unfold remove_Revocation.
      apply filter_In.
      split.
      apply H.
      apply Bool.negb_true_iff.
      assumption.
    -
      unfold remove_Revocation in H.
      apply filter_In in H.
      apply H.
  Qed.

  Lemma remove_PNVI_set_mem:
    forall l s,
      is_PNVI_switch s = false ->
      set_mem cerb_switch_dec s (remove_PNVI l) =
        set_mem cerb_switch_dec s l.
  Proof.
    intros l s H.
    apply Bool.eqb_prop.
    unfold Bool.eqb.
    break_match;break_match;auto.
    -
      apply set_mem_correct1 in Heqb.
      apply set_mem_complete1 in Heqb0.
      apply remove_PNVI_In in Heqb;auto.
    -
      apply set_mem_correct1 in Heqb0.
      apply set_mem_complete1 in Heqb.
      apply remove_PNVI_In in Heqb0;auto.
  Qed.

  Lemma remove_Revocation_set_mem:
    forall l s,
      is_Revocation_switch s = false ->
      set_mem cerb_switch_dec s (remove_Revocation l) =
        set_mem cerb_switch_dec s l.
  Proof.
    intros l s H.
    apply Bool.eqb_prop.
    unfold Bool.eqb.
    break_match;break_match;auto.
    -
      apply set_mem_correct1 in Heqb.
      apply set_mem_complete1 in Heqb0.
      apply remove_Revocation_In in Heqb;auto.
    -
      apply set_mem_correct1 in Heqb0.
      apply set_mem_complete1 in Heqb.
      apply remove_Revocation_In in Heqb0;auto.
  Qed.

  Lemma remove_Revocation_correct:
    forall l s, is_Revocation_switch s = true -> ~(set_In s (remove_Revocation l)).
  Proof.
    intros l.
    induction l;intros.
    - auto.
    - cbn.
      destruct (cerb_switch_dec a s) as [E|NE].
      +
        subst.
        break_match.
        * apply negb_true_iff in Heqb; congruence.
        * apply IHl; auto.
      +
        break_match.
        *
          cbn.
          intros [C1 |C2].
          -- congruence.
          -- contradict C2; apply IHl; assumption.
        * apply IHl; assumption.
  Qed.

  (* All non-pnvi and non-revocation switches are the same *)
  Lemma non_PNVI_switches_match (s: cerb_switch):
    (is_PNVI_switch s = false /\ s <> SW_revocation INSTANT) ->
    has_switch (WithPNVISwitches.get_switches tt) s =
      has_switch (WithoutPNVISwitches.get_switches tt) s.
  Proof.
    intros [HP HR].
    unfold WithPNVISwitches.get_switches, WithoutPNVISwitches.get_switches.
    generalize (abst_get_switches tt) as l.
    intros l.
    pose proof (set_In_dec cerb_switch_dec s l) as D.
    unfold is_PNVI_switch in HP.
    unfold is_Revocation_switch in HR.

    Ltac one_has_switch D
      :=
      unfold has_switch;
      apply eqb_true_iff;
      unfold Bool.eqb;
      destruct D as [IN | NIN];
      [
        repeat break_match; try tauto;
        match goal with
        | [H: set_mem _ _ _ = false |- _] =>
            apply set_mem_complete1 in H;
            contradict H;
            apply set_add_intro1;
            apply -> remove_Revocation_In;auto;
            apply -> remove_PNVI_In;auto
        end
      |
        repeat break_match; try tauto;
        match goal with
        | [H: set_mem _ _ _ = true |- _] =>
            apply set_mem_correct1 in H;
            contradict NIN;
            apply set_add_elim in H;
            destruct H as [H1 |H2];
            [inversion H1 |
              apply remove_Revocation_In in H2; auto;
              apply remove_PNVI_In in H2; auto]
        end
      ].

    destruct s eqn:S; invc HP; try invc HR; try one_has_switch D.
    destruct s0;[congruence|].
    unfold has_switch.
    apply eqb_true_iff.
    unfold Bool.eqb.
    repeat break_match;auto;
      match goal with
      | [H: set_mem _ _ _ = true |- _] =>
          apply set_mem_correct1 in H;
          apply set_add_elim in H;
          destruct H as [H1 |H2]; [inversion H1|];
          contradict H2;
          apply remove_Revocation_correct;
          auto
      end.
  Qed.

  Lemma has_INSTANT_WithPNVI:
    has_switch (WithPNVISwitches.get_switches tt) (SW_revocation INSTANT) = false.
  Proof.
    unfold has_switch.
    unfold WithPNVISwitches.get_switches.
    apply set_mem_complete2.
    intros C.
    apply set_add_elim in C.
    destruct C as [C1 |C2]; [inversion C1|].
    contradict C2.
    apply remove_Revocation_correct.
    auto.
  Qed.


  (* We normalize, if possible, towards [WithPNVISwitches] *)
  Ltac normalize_switches
    :=
    match goal with
    | [H: context[has_switch (WithPNVISwitches.get_switches tt) (SW_revocation INSTANT)] |- _] =>
        replace (has_switch (WithPNVISwitches.get_switches tt) (SW_revocation INSTANT))
        with false in H by (symmetry;apply has_INSTANT_WithPNVI)
    | [H: context[has_PNVI (WithPNVISwitches.get_switches tt)] |- _] =>
        replace (has_PNVI (WithPNVISwitches.get_switches tt))
        with true in H by has_PNVI_WithPNVI
    | [H: context[has_PNVI (WithoutPNVISwitches.get_switches tt)] |- _] =>
        replace (has_PNVI (WithoutPNVISwitches.get_switches tt))
        with false in H by CheriMemoryWithoutPNVI.resolve_has_PNVI
    | [H: context[has_switch (WithoutPNVISwitches.get_switches tt) ?s] |- _] =>
        match s with
        | SW_PNVI _ => fail
        | SW_revocation _ => fail
        | _ =>
            replace (has_switch (WithoutPNVISwitches.get_switches tt) s) with
            (has_switch (WithPNVISwitches.get_switches tt) s)
            in H by (apply non_PNVI_switches_match;auto)
        end
    | [|- context[has_switch (WithoutPNVISwitches.get_switches tt) ?s]] =>
        match s with
        | SW_PNVI _ => fail
        | SW_revocation _ => fail
        | _ =>
            replace (has_switch (WithoutPNVISwitches.get_switches tt) s) with
            (has_switch (WithPNVISwitches.get_switches tt) s)
            by (apply non_PNVI_switches_match;auto)
        end
    | [ |- context[has_PNVI (WithPNVISwitches.get_switches tt)]] =>
        setoid_replace (has_PNVI (WithPNVISwitches.get_switches tt))
        with true by (apply has_PNVI_WithPNVI)
    | [|- context[has_PNVI (WithoutPNVISwitches.get_switches tt)]] =>
        replace (has_PNVI (WithoutPNVISwitches.get_switches tt))
        with false by (symmetry;apply CheriMemoryWithoutPNVI.resolve_has_PNVI)
    end.

  (* --- Lemmas about memory models --- *)

  (* TODO: maybe incomplete *)
  Theorem models_compatible:
    CheriMemoryWithPNVI.initial_address = CheriMemoryWithoutPNVI.initial_address /\
      CheriMemoryWithPNVI.DEFAULT_FUEL = CheriMemoryWithoutPNVI.DEFAULT_FUEL /\
      CheriMemoryWithPNVI.MAX_STRFCAP_FORMAT_LEN = CheriMemoryWithoutPNVI.MAX_STRFCAP_FORMAT_LEN /\
      CheriMemoryWithPNVI.zero_fval = CheriMemoryWithoutPNVI.zero_fval /\
      CheriMemoryWithPNVI.one_fval = CheriMemoryWithoutPNVI.one_fval.
  Proof.
    repeat split;cbv.
  Qed.

  Theorem null_ptrval_same:
    forall m1 m2 t,
      ptr_value_same m1 m2
        (CheriMemoryWithPNVI.null_ptrval t)
        (CheriMemoryWithoutPNVI.null_ptrval t).
  Proof.
    intros m1 m2 t.
    unfold CheriMemoryWithPNVI.null_ptrval, CheriMemoryWithoutPNVI.null_ptrval.
    unfold CheriMemoryWithPNVI.PNVI_prov, CheriMemoryWithoutPNVI.PNVI_prov.
    repeat normalize_switches.
    constructor.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.null_ptrval CheriMemoryWithoutPNVI.null_ptrval.

  Theorem concrete_ptrval_same:
    forall m1 m2 n a,
      serr_eq (ptr_value_same m1 m2)
        (CheriMemoryWithPNVI.concrete_ptrval n a)
        (CheriMemoryWithoutPNVI.concrete_ptrval n a).
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.concrete_ptrval CheriMemoryWithoutPNVI.concrete_ptrval.

  Theorem fun_ptrval_same:
    forall m1 m2 s,
      serr_eq (ptr_value_same m1 m2)
        (CheriMemoryWithPNVI.fun_ptrval s)
        (CheriMemoryWithoutPNVI.fun_ptrval s).
  Proof.
    intros m1 m2 s.
    cbn.
    unfold CheriMemoryWithPNVI.PNVI_prov, CheriMemoryWithoutPNVI.PNVI_prov.
    repeat normalize_switches.
    constructor.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.fun_ptrval CheriMemoryWithoutPNVI.fun_ptrval.

  (* TODO: this should be part of capabilities library *)
  Lemma cap_invalidate_preserves_ghost_state:
    forall c : Capability_GS.t,
      Capability_GS.get_ghost_state c = Capability_GS.get_ghost_state (Capability_GS.cap_invalidate c).
  Proof.
    intros c.
    destruct c.
    unfold Capability_GS.cap_invalidate, Capability_GS.get_ghost_state.
    reflexivity.
  Qed.

  Lemma single_alloc_id_cap_cmp_value_eq:
    forall m1 alloc_id c1 c2 ,
      single_alloc_id_cap_cmp (CheriMemoryWithPNVI.allocations m1) alloc_id c1 c2
      ->
        Capability_GS.cap_get_value c1 = Capability_GS.cap_get_value c2.
  Proof.
    intros m1 alloc_id c1 c2 Hcmp.
    inversion Hcmp as [a Hmap Hmatch | Hmap Hinv]; subst.
    - (* single_cap_cmp_live case *)
      invc Hmatch.
      reflexivity.
      apply Capability_GS.cap_invalidate_preserves_value.
    - (* single_cap_cmp_dead case *)
      apply Capability_GS.cap_invalidate_preserves_value.
  Qed.

  Theorem case_funsym_opt_same:
    forall m1 m2 p1 p2,
      mem_state_same m1 m2 ->
      ptr_value_same m1 m2 p1 p2 ->
      (CheriMemoryWithPNVI.case_funsym_opt m1 p1 =
         CheriMemoryWithoutPNVI.case_funsym_opt m2 p2).
  Proof.
    cbn.
    intros m1 m2 [p1prov p1v] [p2prov p2v] ME FE.
    invc FE;
      unfold CheriMemoryWithPNVI.case_funsym_opt, CheriMemoryWithPNVI.break_PV,
      CheriMemoryWithoutPNVI.case_funsym_opt, CheriMemoryWithoutPNVI.break_PV.

    Ltac solve_zmap_find ME Mfuncs :=
      unfold CheriMemoryWithPNVI.cap_to_Z, CheriMemoryWithoutPNVI.cap_to_Z;
      pose models_compatible as C;
      destruct C as [CI _];
      rewrite CI;
      destruct_mem_state_same ME;
      unfold ZMap.Equal in Mfuncs;
      rewrite Mfuncs;
      reflexivity.

    -
      break_match_goal; [
          break_match_goal;[reflexivity | solve_zmap_find ME Mfuncs]
        | solve_zmap_find ME Mfuncs].
    -
      (* same as previous *)
      break_match_goal; [
          break_match_goal;[reflexivity | solve_zmap_find ME Mfuncs]
        | solve_zmap_find ME Mfuncs].
    -
      break_match_goal;[reflexivity|solve_zmap_find ME Mfuncs].

    -
      unfold CheriMemoryWithPNVI.cap_to_Z, CheriMemoryWithoutPNVI.cap_to_Z.
      pose models_compatible as C.
      destruct C as [CI _].
      rewrite CI. clear CI.
      destruct_mem_state_same ME.
      unfold ZMap.Equal in Mfuncs.
      rewrite Mfuncs; clear Mfuncs.

      apply single_alloc_id_cap_cmp_value_eq in H0.
      rewrite H0.
      reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.case_funsym_opt CheriMemoryWithoutPNVI.case_funsym_opt.

  Theorem derive_cap_same:
    forall is_signed bop ival1 ival2,
      CheriMemoryWithPNVI.derive_cap is_signed bop ival1 ival2 =
        CheriMemoryWithoutPNVI.derive_cap is_signed bop ival1 ival2.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.derive_cap CheriMemoryWithoutPNVI.derive_cap.

  Theorem cap_assign_value_same:
    forall loc ival_cap ival_n,
      CheriMemoryWithPNVI.cap_assign_value loc ival_cap ival_n =
        CheriMemoryWithoutPNVI.cap_assign_value loc ival_cap ival_n.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.cap_assign_value CheriMemoryWithoutPNVI.cap_assign_value.

  Theorem ptr_t_int_value_same:
    forall p,
      CheriMemoryWithPNVI.ptr_t_int_value p =
        CheriMemoryWithoutPNVI.ptr_t_int_value p.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.ptr_t_int_value CheriMemoryWithoutPNVI.ptr_t_int_value.

  Theorem null_cap_same:
    forall f,
      CheriMemoryWithPNVI.null_cap f =
        CheriMemoryWithoutPNVI.null_cap f.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.null_cap CheriMemoryWithoutPNVI.null_cap.

  Theorem array_shift_ptrval_same:
    forall pv ct iv,
      CheriMemoryWithPNVI.array_shift_ptrval pv ct iv =
        CheriMemoryWithoutPNVI.array_shift_ptrval pv ct iv.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.array_shift_ptrval CheriMemoryWithoutPNVI.array_shift_ptrval.

  Theorem member_shift_ptrval_same:
    forall pv ct ci,
      CheriMemoryWithPNVI.member_shift_ptrval pv ct ci =
        CheriMemoryWithoutPNVI.member_shift_ptrval pv ct ci.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.member_shift_ptrval CheriMemoryWithoutPNVI.member_shift_ptrval.

  Theorem concurRead_ival_same:
    forall ct cs,
      CheriMemoryWithPNVI.concurRead_ival ct cs =
        CheriMemoryWithoutPNVI.concurRead_ival ct cs.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.concurRead_ival CheriMemoryWithoutPNVI.concurRead_ival.

  Theorem integer_ival_same:
    forall n,
      CheriMemoryWithPNVI.integer_ival n =
        CheriMemoryWithoutPNVI.integer_ival n.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.integer_ival CheriMemoryWithoutPNVI.integer_ival.

  Theorem max_ival_same:
    forall ct,
      CheriMemoryWithPNVI.max_ival ct =
        CheriMemoryWithoutPNVI.max_ival ct.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.max_ival CheriMemoryWithoutPNVI.max_ival.

  Theorem min_ival_same:
    forall ct,
      CheriMemoryWithPNVI.min_ival ct =
        CheriMemoryWithoutPNVI.min_ival ct.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.min_ival CheriMemoryWithoutPNVI.min_ival.

  Theorem op_ival_same:
    forall op a b,
      CheriMemoryWithPNVI.op_ival op a b =
        CheriMemoryWithoutPNVI.op_ival op a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.op_ival CheriMemoryWithoutPNVI.op_ival.

  Lemma alignof_same:
    forall fuel maybe_tagDefs ty,
      CheriMemoryWithPNVI.alignof fuel maybe_tagDefs ty =
        CheriMemoryWithoutPNVI.alignof fuel maybe_tagDefs ty.
  Proof.
    intros fuel maybe_tagDefs ty.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.alignof CheriMemoryWithoutPNVI.alignof.

  Theorem alignof_ival_same:
    forall ty,
      CheriMemoryWithPNVI.alignof_ival ty =
        CheriMemoryWithoutPNVI.alignof_ival ty.
  Proof.
    intros ty.
    unfold CheriMemoryWithPNVI.alignof_ival, CheriMemoryWithoutPNVI.alignof_ival.
    unfold CheriMemoryWithPNVI.DEFAULT_FUEL, CheriMemoryWithoutPNVI.DEFAULT_FUEL.
    cbn.
    repeat break_match;rewrite alignof_same in Heqs;rewrite Heqs in Heqs0;inv Heqs0; reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.alignof_ival CheriMemoryWithoutPNVI.alignof_ival.

  Lemma offsetof_same:
    forall fuel tagDefs tag_sym,
      CheriMemoryWithPNVI.offsetsof fuel tagDefs tag_sym =
        CheriMemoryWithoutPNVI.offsetsof fuel tagDefs tag_sym.
  Proof.
    intros fuel tagDefs tag_sym.
    destruct fuel; [reflexivity|].
    cbn.
    break_match; [|reflexivity].
    break_match; [|reflexivity].
    remember (monadic_fold_left _ _ _) as f1.
    break_match.
    reflexivity.
    break_let.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.offsetsof CheriMemoryWithoutPNVI.offsetsof.

  Theorem offsetof_ival_same:
    forall tagDefs tag_sym memb_ident,
      CheriMemoryWithPNVI.offsetof_ival tagDefs tag_sym memb_ident =
        CheriMemoryWithoutPNVI.offsetof_ival tagDefs tag_sym memb_ident.
  Proof.
    intros tagDefs tag_sym memb_ident.
    cbn.
    unfold CheriMemoryWithPNVI.DEFAULT_FUEL, CheriMemoryWithoutPNVI.DEFAULT_FUEL.
    cbn.
    repeat break_match; rewrite offsetof_same in Heqs; rewrite Heqs in Heqs0; inv Heqs0 ; try reflexivity;
      rewrite Heqo in Heqo0;
      inv Heqo0; reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.offsetof_ival CheriMemoryWithoutPNVI.offsetof_ival.

  (* TODO: [ty] is missing *)
  Lemma sizeof_same:
    forall fuel maybe_tagDefs,
      CheriMemoryWithPNVI.sizeof fuel maybe_tagDefs =
        CheriMemoryWithoutPNVI.sizeof fuel maybe_tagDefs.
  Proof.
    intros fuel maybe_tagDefs.
    destruct fuel; [reflexivity|].
    cbn.
    break_match; [|reflexivity].
    f_equiv.
  Qed.
  Opaque CheriMemoryWithPNVI.sizeof CheriMemoryWithoutPNVI.sizeof.

  Theorem sizeof_ival_same:
    forall ty,
      CheriMemoryWithPNVI.sizeof_ival ty =
        CheriMemoryWithoutPNVI.sizeof_ival ty.
  Proof.
    intros ty.
    cbn.
    unfold CheriMemoryWithPNVI.DEFAULT_FUEL, CheriMemoryWithoutPNVI.DEFAULT_FUEL.
    repeat break_match; rewrite sizeof_same in Heqs; rewrite Heqs in Heqs0; inv Heqs0 ; try reflexivity;
      rewrite Heqo in Heqo0;
      inv Heqo0; reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.sizeof_ival CheriMemoryWithoutPNVI.sizeof_ival.

  Theorem bitwise_complement_ival_same:
    forall ty v,
      CheriMemoryWithPNVI.bitwise_complement_ival ty v =
        CheriMemoryWithoutPNVI.bitwise_complement_ival ty v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.bitwise_complement_ival CheriMemoryWithoutPNVI.bitwise_complement_ival.

  Theorem bitwise_and_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_and_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_and_ival ty a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.bitwise_and_ival CheriMemoryWithoutPNVI.bitwise_and_ival.

  Theorem bitwise_or_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_or_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_or_ival ty a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.bitwise_or_ival CheriMemoryWithoutPNVI.bitwise_or_ival.

  Theorem bitwise_xor_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_xor_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_xor_ival ty a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.bitwise_xor_ival CheriMemoryWithoutPNVI.bitwise_xor_ival.

  Theorem is_specified_ival_same:
    forall v,
      CheriMemoryWithPNVI.is_specified_ival v =
        CheriMemoryWithoutPNVI.is_specified_ival v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.is_specified_ival CheriMemoryWithoutPNVI.is_specified_ival.

  Theorem eq_ival_same:
    forall a b,
      CheriMemoryWithPNVI.eq_ival a b =
        CheriMemoryWithoutPNVI.eq_ival a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.eq_ival CheriMemoryWithoutPNVI.eq_ival.

  Theorem lt_ival_same:
    forall a b,
      CheriMemoryWithPNVI.lt_ival a b =
        CheriMemoryWithoutPNVI.lt_ival a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.lt_ival CheriMemoryWithoutPNVI.lt_ival.

  Theorem le_ival_same:
    forall a b,
      CheriMemoryWithPNVI.le_ival a b =
        CheriMemoryWithoutPNVI.le_ival a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.le_ival CheriMemoryWithoutPNVI.le_ival.

  Theorem str_fval_same:
    forall v,
      CheriMemoryWithPNVI.str_fval v =
        CheriMemoryWithoutPNVI.str_fval v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.str_fval CheriMemoryWithoutPNVI.str_fval.

  Definition op_fval_same:
    forall fop a b,
      CheriMemoryWithPNVI.op_fval fop a b =
        CheriMemoryWithoutPNVI.op_fval fop a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.op_fval CheriMemoryWithoutPNVI.op_fval.

  Theorem eq_fval_same:
    forall a b,
      CheriMemoryWithPNVI.eq_fval a b =
        CheriMemoryWithoutPNVI.eq_fval a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.eq_fval CheriMemoryWithoutPNVI.eq_fval.

  Theorem lt_fval_same:
    forall a b,
      CheriMemoryWithPNVI.lt_fval a b =
        CheriMemoryWithoutPNVI.lt_fval a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.lt_fval CheriMemoryWithoutPNVI.lt_fval.

  Theorem le_fval_same:
    forall a b,
      CheriMemoryWithPNVI.le_fval a b =
        CheriMemoryWithoutPNVI.le_fval a b.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.le_fval CheriMemoryWithoutPNVI.le_fval.

  Theorem fvfromint_same:
    forall v,
      CheriMemoryWithPNVI.fvfromint v =
        CheriMemoryWithoutPNVI.fvfromint v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.fvfromint CheriMemoryWithoutPNVI.fvfromint.

  Theorem ivfromfloat_same:
    forall t v,
      CheriMemoryWithPNVI.ivfromfloat t v =
        CheriMemoryWithoutPNVI.ivfromfloat t v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.ivfromfloat CheriMemoryWithoutPNVI.ivfromfloat.

  Theorem unspecified_mval_same:
    forall t,
      CheriMemoryWithPNVI.unspecified_mval t =
        CheriMemoryWithoutPNVI.unspecified_mval t.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.unspecified_mval CheriMemoryWithoutPNVI.unspecified_mval.

  Theorem integer_value_mval_same:
    forall t v,
      CheriMemoryWithPNVI.integer_value_mval t v =
        CheriMemoryWithoutPNVI.integer_value_mval t v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.integer_value_mval CheriMemoryWithoutPNVI.integer_value_mval.

  Theorem floating_value_mval_same:
    forall t v,
      CheriMemoryWithPNVI.floating_value_mval t v =
        CheriMemoryWithoutPNVI.floating_value_mval t v.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.floating_value_mval CheriMemoryWithoutPNVI.floating_value_mval.

  (* This theorem using weaker equality, since pointers are involved *)
  Theorem pointer_mval_same:
    forall m1 m2 t p1 p2,
      ptr_value_same m1 m2 p1 p2 ->
      mem_value_indt_same m1 m2 (CheriMemoryWithPNVI.pointer_mval t p1)
        (CheriMemoryWithoutPNVI.pointer_mval t p2).
  Proof.
    constructor.
    auto.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem array_mval_same:
    forall m1 m2 a1 a2,
      eqlistA (mem_value_indt_same m1 m2) a1 a2 ->
      mem_value_indt_same m1 m2 (CheriMemoryWithPNVI.array_mval a1)
        (CheriMemoryWithoutPNVI.array_mval a2).
  Proof.
    constructor.
    assumption.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem struct_mval_same:
    forall m1 m2 s1 s2 l1 l2,
      s1 = s2 /\ eqlistA (struct_field_eq m1 m2) l1 l2 ->
      mem_value_indt_same m1 m2 (CheriMemoryWithPNVI.struct_mval s1 l1)
        (CheriMemoryWithoutPNVI.struct_mval s2 l2).
  Proof.
    intros m1 m2 s1 s2 l1 l2 [H1 H2].
    constructor; assumption.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem union_mval_same:
    forall m1 m2 s1 id1 v1 s2 id2 v2,
      s1 = s2 /\ id1 = id2 /\ mem_value_indt_same m1 m2 v1 v2 ->
      mem_value_indt_same m1 m2 (CheriMemoryWithPNVI.union_mval s1 id1 v1)
        (CheriMemoryWithoutPNVI.union_mval s2 id2 v2).
  Proof.
    constructor; assumption.
  Qed.

  Theorem get_intrinsic_type_spec_same:
    forall s,
      CheriMemoryWithPNVI.get_intrinsic_type_spec s =
        CheriMemoryWithoutPNVI.get_intrinsic_type_spec s.
  Proof.
    intros s.
    unfold CheriMemoryWithPNVI.get_intrinsic_type_spec.
    unfold CheriMemoryWithoutPNVI.get_intrinsic_type_spec.
    repeat break_match; auto;
      normalize_switches;congruence.
  Qed.
  Opaque CheriMemoryWithPNVI.get_intrinsic_type_spec CheriMemoryWithoutPNVI.get_intrinsic_type_spec.

  Definition resolve_function_pointer_res_eq
    : relation ((ZMap.t (digest * string * Capability_GS.t)) * Capability_GS.t)
    :=
    fun '(m,c) '(m',c') =>
      c=c' /\ ZMap.Equal m m'.

  Lemma resolve_function_pointer_same:
    forall (m1 m2 : ZMap.t (digest * string * Capability_GS.t)) (fp1 fp2 : function_pointer),
      fp1 = fp2 ->
      ZMap.Equal m1 m2 ->
      resolve_function_pointer_res_eq
        (CheriMemoryWithPNVI.resolve_function_pointer m1 fp1)
        (CheriMemoryWithoutPNVI.resolve_function_pointer m2 fp2).
  Proof.
    intros m1 m2 fp1 fp2 Ef Em.
    subst fp2.
    unfold CheriMemoryWithPNVI.resolve_function_pointer, CheriMemoryWithoutPNVI.resolve_function_pointer.
    destruct fp1.
    -
      destruct s.
      unfold resolve_function_pointer_res_eq.
      repeat break_let;

        rewrite Em in Heqp; break_match; repeat break_let; repeat tuple_inversion;
        split; try assumption; try reflexivity.

      destruct s; try assumption.
      rewrite Em.
      solve_proper.
    -
      cbn.
      split;[reflexivity|assumption].
  Qed.

  Lemma ghost_tags_same:
    forall m1 m2 (addr : AddressValue.t) (sz0 sz1:Z) (capmeta0 capmeta1 : ZMap.t (bool * CapGhostState)),
      sz0 = sz1 ->
      capmeta_same m1 m2 capmeta0 capmeta1 ->
      capmeta_same m1 m2
        (CheriMemoryWithPNVI.ghost_tags addr sz0 capmeta0)
        (CheriMemoryWithoutPNVI.ghost_tags addr sz1 capmeta1).
  Proof.
    intros m1 m2 addr sz0 sz1 capmeta0 capmeta1 Hsz H.
    subst sz1.
    unfold CheriMemoryWithPNVI.ghost_tags, CheriMemoryWithoutPNVI.ghost_tags.

    match goal with
      [ |- context[ZMap.mapi ?ff _]] => remember ff as f
    end.

    unfold capmeta_same, zmap_relate_keys.
    intros k.
    specialize (H k).
    destruct H as [[v1 [v2 [I0 [I1 S]]]] | [N1 N2]].
    -
      (* [k] in [capmeta0] and [capmeta1] *)
      left.
      apply ZMap.mapi_1 with (f:=f) in I0, I1.
      destruct I0 as [k0 [E0 M0]].
      destruct I1 as [k1 [E1 M1]].
      subst k0 k1.
      exists (f k v1), (f k v2).

      split; auto.
      split; auto.
      inversion S;[constructor|].
      subst v2 v1 addr0 m3 m1.
      destruct gs1, gs2.
      cbn in *.
      repeat (break_match_hyp; try some_none).

      (*

      apply mapi_mapsto_iff in M0; [| intros; subst; reflexivity].
      destruct M0 as [v0' [FE0 M0]].

      apply mapi_mapsto_iff in M1; [| intros; subst; reflexivity].
      destruct M1 as [v1' [FE1 M1]].
 *)
      subst tag_unspecified0 bounds_unspecified0.
      remember (f k (false, {| tag_unspecified := false; bounds_unspecified := bounds_unspecified |})) as f1 eqn:F1.
      rewrite Heqf in F1.
      cbv in F1.
      subst f1.

      remember (f k (true, {| tag_unspecified := tag_unspecified; bounds_unspecified := bounds_unspecified |})) as f0 eqn:F0.
      rewrite Heqf in F0.
      break_match;subst f0; cbn in *.
      +
        clear M0 M1.
        clear f Heqf.
        invc S.
        cbn in *.
        repeat (break_match_hyp; try some_none).
        econstructor; eauto;
          (unfold decode_cap_at;
           cbn;
           break_match;[repeat some_inv;auto| congruence]).
      +
        clear M0 M1.
        clear f Heqf.
        invc S.
        cbn in *.
        repeat (break_match_hyp; try some_none).
        econstructor; eauto;
          (unfold decode_cap_at;
           cbn;
           break_match;[repeat some_inv;auto| congruence]).
    -
      (* [k] not in [capmeta0] and [capmeta1] *)
      right.
      split.
      +
        intros [x H].
        contradict N1.
        apply mapi_mapsto_iff in H.
        *
          destruct H as [y [H1 H2]].
          exists y.
          apply H2.
        *
          intros x0 y e H1.
          subst x0.
          reflexivity.
      +
        intros [x H].
        contradict N2.
        apply mapi_mapsto_iff in H.
        *
          destruct H as [y [H1 H2]].
          exists y.
          apply H2.
        *
          intros x0 y e H1.
          subst x0.
          reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.ghost_tags CheriMemoryWithoutPNVI.ghost_tags.

  Theorem cap_match_dyn_allocation_same:
    forall t1 t2 a1 a2,
      t1 = t2 /\ a1 = a2 ->
      CheriMemoryWithPNVI.cap_match_dyn_allocation t1 a1 =
        CheriMemoryWithoutPNVI.cap_match_dyn_allocation t2 a2.
  Proof.
    intros t1 t2 a1 a2 [ET EA].
    unfold CheriMemoryWithPNVI.cap_match_dyn_allocation, CheriMemoryWithoutPNVI.cap_match_dyn_allocation.
    subst.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.cap_match_dyn_allocation CheriMemoryWithoutPNVI.cap_match_dyn_allocation.

  Theorem is_pointer_algined_same:
    forall p,
      CheriMemoryWithPNVI.is_pointer_algined p = CheriMemoryWithoutPNVI.is_pointer_algined p.
  Proof.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.is_pointer_algined CheriMemoryWithoutPNVI.is_pointer_algined.

  (* return type of [repr] *)
  Definition repr_res_t:Type := ZMap.t (digest * string * Capability_GS.t)
                                         * ZMap.t (bool * CapGhostState)
                                         * list AbsByte.

  Definition repr_res_eq
    (mem1:CheriMemoryWithPNVI.mem_state_r)
    (mem2:CheriMemoryWithoutPNVI.mem_state_r)
    (addr : Z)
    : relation (repr_res_t)
    :=
    fun '(funptrmap, capmeta, bytes) '(funptrmap', capmeta', bytes') =>

      let bytemap  := zmap_add_list_at mem1.(CheriMemoryWithPNVI.bytemap   ) bytes  addr in
      let bytemap' := zmap_add_list_at mem2.(CheriMemoryWithoutPNVI.bytemap) bytes' addr in
      let mem1' :=
        CheriMemoryWithPNVI.mem_state_with_funptrmap_bytemap_capmeta funptrmap bytemap capmeta mem1 in
      let mem2' :=
        CheriMemoryWithoutPNVI.mem_state_with_funptrmap_bytemap_capmeta funptrmap' bytemap' capmeta' mem2 in

      ZMap.Equal funptrmap funptrmap'
      /\ capmeta_same mem1' mem2' capmeta capmeta'
      /\ eqlistA AbsByte_eq bytes bytes'.

  Section repr_same_proof.

    Lemma capmeta_add_eq_same
      (mem1:CheriMemoryWithPNVI.mem_state_r)
      (mem2:CheriMemoryWithoutPNVI.mem_state_r)
      (addr : Z)
      (capmeta1 capmeta2 : ZMap.t (bool * CapGhostState)):
      capmeta_same mem1 mem2 capmeta1 capmeta2 ->
      forall t : Capability_GS.t,
        capmeta_same mem1 mem2
          (ZMap.add addr (Capability_GS.cap_is_valid t, Capability_GS.get_ghost_state t) capmeta1)
          (ZMap.add addr (Capability_GS.cap_is_valid t, Capability_GS.get_ghost_state t) capmeta2).
    Proof.
      intros Ecap c.
      unfold capmeta_same, zmap_relate_keys in *.
      intros k.
      specialize (Ecap k).
      destruct Ecap as [[v1 [v2 [I0 [I1 S]]]] | [N1 N2]].
      -
        left.
        destruct (Z.eq_dec k addr).
        +
          subst k.
          exists (Capability_GS.cap_is_valid c, Capability_GS.get_ghost_state c), (Capability_GS.cap_is_valid c, Capability_GS.get_ghost_state c).
          repeat split.
          1,2: apply ZMap.add_1;reflexivity.
          constructor;split;reflexivity.
        +
          eexists.
          eexists.
          repeat split.
          1,2: apply ZMap.add_2;auto;eassumption.
          assumption.
      -
        destruct (Z.eq_dec k addr).
        +
          left.
          subst k.
          exists (Capability_GS.cap_is_valid c, Capability_GS.get_ghost_state c), (Capability_GS.cap_is_valid c, Capability_GS.get_ghost_state c).
          repeat split.
          1,2: apply ZMap.add_1;reflexivity.
          constructor;split;reflexivity.
        +
          right.
          split.
          *
            contradict N1.
            destruct N1.
            exists x.
            apply ZMap.add_3 in H;auto.
          *
            contradict N2.
            destruct N2.
            exists x.
            apply ZMap.add_3 in H;auto.
    Qed.


    Lemma update_capmeta_single_alloc_same
      (mem1:CheriMemoryWithPNVI.mem_state_r)
      (mem2:CheriMemoryWithoutPNVI.mem_state_r)
      (c2 c1 : Capability_GS.t)
      (alloc_id : ZMap.key)
      (addr : Z)
      (capmeta1 capmeta2 : ZMap.t (bool * CapGhostState))
      (bytes1 bytes2: list ascii)
      (tag1 tag2: bool)
      :
      capmeta_same mem1 mem2 capmeta1 capmeta2 ->
      Capability_GS.encode true c1 = Some (bytes1, tag1) ->
      Capability_GS.encode true c2 = Some (bytes2, tag2) ->
      single_alloc_id_cap_cmp (CheriMemoryWithPNVI.allocations mem1) alloc_id c1 c2
      ->
        capmeta_same mem1 mem2
          (CheriMemoryWithPNVI.update_capmeta c1 addr capmeta1)
          (CheriMemoryWithoutPNVI.update_capmeta c2 addr capmeta2).
    Proof.
      intros Ecap E1 E2 H.
      unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
      rewrite is_pointer_algined_same.
      destruct (CheriMemoryWithoutPNVI.is_pointer_algined addr) eqn:A ; [|assumption].
      invc H.
      - (* `single_cap_cmp_live` constructor: `alloc_id` is live *)
        unfold capmeta_same , zmap_relate_keys.
        intros k.
        invc H1.
        + (* `cap_match_alloc_match` constructor: allocation/cap match *)
          subst.
          destruct (Z.eq_dec k addr).
          *
            left.
            subst k.
            exists (Capability_GS.cap_is_valid c2, Capability_GS.get_ghost_state c2), (Capability_GS.cap_is_valid c2, Capability_GS.get_ghost_state c2).
            repeat split.
            1,2: apply ZMap.add_1;reflexivity.
            constructor;split;try reflexivity.
          *
            setoid_rewrite add_neq_mapsto_iff;auto.
        + (* `cap_match_with_alloc_mismatch` constructor: alloc/cap mis-match *)
          destruct (Z.eq_dec k addr).
          * (* cap which is being added *)
            subst k.
            left.
            repeat rewrite Capability_GS.cap_invalidate_invalidates.
            repeat rewrite <- cap_invalidate_preserves_ghost_state.
            exists (Capability_GS.cap_is_valid c1, Capability_GS.get_ghost_state c1).
            exists (false, Capability_GS.get_ghost_state c1).
            split. apply ZMap.add_1; reflexivity.
            split. apply ZMap.add_1; reflexivity.
            destruct (Capability_GS.cap_is_valid c1).
            --
              (* revocation case *)
              unfold capmeta_same , zmap_relate_keys in Ecap.
              specialize (Ecap addr).
              destruct Ecap as [[v1 [v2 [I0 [I1 S]]]] | [N1 N2]].
              ++
                remember
                  (mapi
                     (fun (i_value : nat) (b_value : ascii) =>
                        CheriMemoryWithPNVI.absbyte_v (Prov_some alloc_id) (Some i_value) (Some b_value)) bytes1) as bs1.
                remember (mapi
                            (fun (i_value : nat) (b_value : ascii) =>
                               CheriMemoryWithoutPNVI.absbyte_v Prov_disabled (Some i_value) (Some b_value)) bytes2) as bs2.

                econstructor 2 with (c1:=c1) (c2:=c1) (prov:=Prov_some alloc_id)
                                    (bs1:=bs1) (bs2:=bs2); auto; admit.

              (* HERE. We refer to bytes which has not been changed yet.
                   Conculusion: using `capmeta_same` instead of `repr_res_same` is wrong *)
              ++
                admit.
            --
              constructor.
          * (* all other caps unchanged *)
            setoid_rewrite add_neq_mapsto_iff;auto.
      - (* `single_cap_cmp_dead` consturctor: `alloc_id` is dead *)
        admit.
    Admitted.

    Definition repr_fold_T:Type :=
      ZMap.t (digest * string * Capability_GS.t)
      * ZMap.t (bool * CapGhostState)
      * Z
      * list (list AbsByte).

    Definition repr_fold_eq
      (mem1:CheriMemoryWithPNVI.mem_state_r)
      (mem2:CheriMemoryWithoutPNVI.mem_state_r)
      : relation repr_fold_T
      :=
      fun '(funptrmap,capmeta,a,lbytes) '(funptrmap',capmeta',a',lbytes') =>
        let bs  := List.concat (List.rev lbytes ) in (* TODO: do we need 'rev' here? *)
        let bs' := List.concat (List.rev lbytes') in (* TODO: do we need 'rev' here? *)
        a = a'
        /\ repr_res_eq mem1 mem2 (a - (Z.of_nat (List.length bs)))
             (funptrmap  , capmeta  , bs )
             (funptrmap' , capmeta' , bs').

    Definition repr_fold2_T:Type :=
      ZMap.t (digest * string * Capability_GS.t)
      * ZMap.t (bool * CapGhostState)
      * Z
      * list AbsByte.

    Definition repr_fold2_eq
      (mem1:CheriMemoryWithPNVI.mem_state_r)
      (mem2:CheriMemoryWithoutPNVI.mem_state_r)
      (addr : Z)
      : relation repr_fold2_T
      :=
      fun '(funptrmap,capmeta,a,bytes) '(funptrmap',capmeta',a',bytes') =>
        a = a'
        /\ repr_res_eq mem1 mem2 addr
             (funptrmap, capmeta,  bytes )
             (funptrmap',capmeta', bytes').

    Theorem repr_same:
      forall m1 m2 fuel funptrmap1 funptrmap2 capmeta1 capmeta2 addr1 addr2 mval1 mval2,
        ZMap.Equal funptrmap1 funptrmap2
        /\ capmeta_same m1 m2 capmeta1 capmeta2
        /\ addr1 = addr2
        /\  mem_value_indt_same m1 m2 mval1 mval2 ->
        serr_eq (repr_res_eq m1 m2 addr1)
          (CheriMemoryWithPNVI.repr    fuel funptrmap1 capmeta1 addr1 mval1)
          (CheriMemoryWithoutPNVI.repr fuel funptrmap2 capmeta2 addr2 mval2).
    Proof.
    (*
      intros m1 m2 fuel funptrmap1 funptrmap2 capmeta1 capmeta2 addr1 addr2 mval1 mval2
        [Ffun [Ecap [Eaddr Emval]]].
      destruct fuel;[reflexivity|].
      subst.

      Opaque is_signed_ity.
      revert fuel addr2 funptrmap1 funptrmap2 Ffun capmeta1 capmeta2 Ecap.
      induction Emval;intros; cbn;
        unfold CheriMemoryWithPNVI.DEFAULT_FUEL, CheriMemoryWithoutPNVI.DEFAULT_FUEL; subst;
        repeat rewrite sizeof_same.
      -
        (* MVunspecified *)
        destruct (CheriMemoryWithoutPNVI.sizeof 1000 None t2); [reflexivity|].
        destruct_serr_eq; try inl_inr.
        rewrite <- Hserr, <- Hserr0. clear Hserr Hserr0.

        constructor;auto.
        split.
        +
          admit.
          (* apply ghost_tags_same; [reflexivity|assumption]. *)
        +
          unfold CheriMemoryWithPNVI.PNVI_prov.
          unfold CheriMemoryWithoutPNVI.PNVI_prov.
          rewrite has_PNVI_WithPNVI, has_PNVI_WithoutPNVI.
          apply list_init_proper;[reflexivity|].
          intros x y E.
          constructor.
          split; auto.
      - (* MVinteger *)
        destruct H as [H0 H1]; subst.
        rename v2 into i0.
        destruct i0 eqn:II0.
        +
          (* i0 = IV z *)
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; try reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; inl_inr.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; inl_inr.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst.
            split; [assumption|].
            split.
            apply ghost_tags_same.
            f_equiv; rewrite 2!map_length; reflexivity.
            assumption.
            unfold CheriMemoryWithPNVI.PNVI_prov.
            unfold CheriMemoryWithoutPNVI.PNVI_prov.
            rewrite has_PNVI_WithPNVI, has_PNVI_WithoutPNVI.
            apply list_map_Proper with (pA:=@eq ascii).
            --
              intros a1 a2 Ea.
              subst.
              constructor.
              cbn.
              auto.
            --
              reflexivity.
        +
          (* i0 = IC b t *)
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; inl_inr.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; inl_inr.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst.
            split; [assumption|].
            split.
            --
              unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
              rewrite is_pointer_algined_same.
              break_match.
              ++ apply capmeta_add_eq_same, Ecap.
              ++ assumption.
            --
              unfold CheriMemoryWithPNVI.PNVI_prov.
              unfold CheriMemoryWithoutPNVI.PNVI_prov.
              rewrite has_PNVI_WithPNVI, has_PNVI_WithoutPNVI.
              apply list_mapi_Proper with (pA:=@eq ascii).
              ++
                intros n a1 a2 Ea.
                subst.
                constructor.
                cbn.
                auto.
              ++
                reflexivity.
      -
        (* MVfloating *)
        destruct H as [H0 H1]; subst.
        rename v2 into i0.
        destruct (CheriMemoryWithoutPNVI.sizeof 1000 None (CoqCtype.Ctype [] (CoqCtype.Basic (CoqCtype.Floating t2)))).
        +
          reflexivity.
        +
          destruct_serr_eq.
          *
            cbn.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            repeat break_match_hyp; inl_inr.
          *
            repeat break_match_hyp; inl_inr.
          *
            break_match; [ inl_inr|].
            break_match_hyp; [ inl_inr|].
            rewrite <- Hserr, <- Hserr0.
            clear Hserr Hserr0.
            cbn.
            split; [assumption|].
            split.
            --
              rewrite 2!map_length.
              apply ghost_tags_same;[reflexivity|assumption].
            --
              unfold CheriMemoryWithPNVI.PNVI_prov.
              unfold CheriMemoryWithoutPNVI.PNVI_prov.
              rewrite has_PNVI_WithPNVI, has_PNVI_WithoutPNVI.
              apply list_map_Proper with (pA:=@eq ascii).
              ++
                intros a1 a2 Ea.
                subst.
                constructor.
                cbn.
                auto.
              ++
                reflexivity.
      -
        (* MVpointer c p *)
        destruct H as [H0 H1]; subst.
        invc H1.
        +
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.

            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s0)) (FP_valid (Symbol d z s0) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            repeat tuple_inversion.
            repeat split.
            --
              assumption.
            --
              unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
              rewrite is_pointer_algined_same.
              break_match.
              ++ apply capmeta_add_eq_same, Ecap.
              ++ assumption.
            --
              rewrite Heqo0 in Heqo.
              invc Heqo.
              unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
              eapply list_mapi_Proper with (pA:=eq).
              intros n x y E.
              constructor.
              cbn. split.
              reflexivity.
              subst.
              reflexivity.
              reflexivity.
            --
              rewrite <- Hserr, <- Hserr0.
              cbn.
              split; [assumption|].
              split.
              ++
                unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
                rewrite is_pointer_algined_same.
                break_match.
                ** apply capmeta_add_eq_same, Ecap.
                ** assumption.
              ++
                unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
                eapply list_mapi_Proper with (pA:=eq).
                intros n x y E.
                constructor.
                cbn. split.
                reflexivity.
                subst.
                reflexivity.
                reflexivity.
            --
              (* same as previous bullet! *)
              rewrite <- Hserr, <- Hserr0.
              cbn.
              split; [assumption|].
              split.
              ++
                unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
                rewrite is_pointer_algined_same.
                break_match.
                ** apply capmeta_add_eq_same, Ecap.
                ** assumption.
              ++
                unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
                eapply list_mapi_Proper with (pA:=eq).
                intros n x y E.
                constructor.
                cbn. split.
                reflexivity.
                subst.
                reflexivity.
                reflexivity.
        +
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.

            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s0)) (FP_valid (Symbol d z s0) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            repeat tuple_inversion.
            repeat split.
            --
              assumption.
            --
              unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
              rewrite is_pointer_algined_same.
              break_match.
              ++ apply capmeta_add_eq_same, Ecap.
              ++ assumption.
            --
              rewrite Heqo0 in Heqo.
              invc Heqo.
              unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
              eapply list_mapi_Proper with (pA:=eq).
              intros n x y E.
              constructor.
              cbn. split.
              reflexivity.
              subst.
              reflexivity.
              reflexivity.
            --
              rewrite <- Hserr, <- Hserr0.
              cbn.
              split; [assumption|].
              split.
              ++
                unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
                rewrite is_pointer_algined_same.
                break_match.
                ** apply capmeta_add_eq_same, Ecap.
                ** assumption.
              ++
                unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
                eapply list_mapi_Proper with (pA:=eq).
                intros n x y E.
                constructor.
                cbn. split.
                reflexivity.
                subst.
                reflexivity.
                reflexivity.
            --
              (* same as previous bullet! *)
              rewrite <- Hserr, <- Hserr0.
              cbn.
              split; [assumption|].
              split.
              ++
                unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
                rewrite is_pointer_algined_same.
                break_match.
                ** apply capmeta_add_eq_same, Ecap.
                ** assumption.
              ++
                unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
                eapply list_mapi_Proper with (pA:=eq).
                intros n x y E.
                constructor.
                cbn. split.
                reflexivity.
                subst.
                reflexivity.
                reflexivity.
        +
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s1)) (FP_valid (Symbol d z s1) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            congruence.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.

            cbn.
            pose proof (resolve_function_pointer_same funptrmap1 funptrmap2 (FP_valid (Symbol d z s0)) (FP_valid (Symbol d z s0) )) as H.
            full_autospecialize H.
            reflexivity.
            assumption.
            unfold resolve_function_pointer_res_eq in H.
            repeat break_let.
            destruct H.
            repeat tuple_inversion.
            repeat split.
            --
              assumption.
            --
              unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
              rewrite is_pointer_algined_same.
              break_match.
              ++ apply capmeta_add_eq_same, Ecap.
              ++ assumption.
            --
              rewrite Heqo0 in Heqo.
              invc Heqo.
              unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
              eapply list_mapi_Proper with (pA:=eq).
              intros n x y E.
              constructor.
              cbn. split.
              reflexivity.
              subst.
              reflexivity.
              reflexivity.
            --
              rewrite <- Hserr, <- Hserr0.
              cbn.
              split; [assumption|].
              split.
              ++
                unfold CheriMemoryWithPNVI.update_capmeta, CheriMemoryWithoutPNVI.update_capmeta.
                rewrite is_pointer_algined_same.
                break_match.
                ** apply capmeta_add_eq_same, Ecap.
                ** assumption.
              ++
                unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
                eapply list_mapi_Proper with (pA:=eq).
                intros n x y E.
                constructor.
                cbn. split.
                reflexivity.
                subst.
                reflexivity.
                reflexivity.
        +
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            admit.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            admit.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.

            cbn.
            remember (mapi
                        (fun (i_value : nat) (b_value : ascii) =>
                           CheriMemoryWithPNVI.absbyte_v (Prov_some alloc_id) (Some i_value) (Some b_value)) l0) as bs1.
            remember (mapi
                        (fun (i_value : nat) (b_value : ascii) =>
                           CheriMemoryWithoutPNVI.absbyte_v Prov_disabled (Some i_value) (Some b_value)) l) as bs2.
            repeat split.
            --
              assumption.
            --
              eapply update_capmeta_single_alloc_same; eauto.
            --
              invc Heqo.
              unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
              eapply list_mapi_Proper with (pA:=eq).
              intros n x y E.
              constructor.
              cbn. split.
              reflexivity.
              subst.
              reflexivity.
              admit.
        +
          destruct_serr_eq.
          *
            cbn.
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; try inl_inr; repeat inl_inr_inv;
              subst; reflexivity.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            admit.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.
            cbn.
            admit.
          *
            unfold option2serr in Hserr, Hserr0.
            repeat break_match_hyp; unfold ret; try inl_inr.
            repeat inl_inr_inv; subst.

            cbn.
            repeat split.
            --
              assumption.
            --
              (* rewrite Ecap.
 *)
              admit.
            --
              invc Heqo.
              unfold CheriMemoryWithPNVI.absbyte_v, CheriMemoryWithoutPNVI.absbyte_v.
              eapply list_mapi_Proper with (pA:=eq).
              intros n x y E.
              constructor.
              cbn. split.
              reflexivity.
              subst.
              reflexivity.
              admit.
      -
        (* MVarray *)
        destruct_serr_eq ; repeat break_match_hyp ; try inl_inr; repeat inl_inr_inv; subst.
        +
          (* error case *)
          cbn.
          cut(@serr_eq repr_fold_T (repr_fold_eq m1 m2)  (inl s) (inl s0));
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold_T.
          rewrite <- Heqs1, <- Heqs2; clear Heqs1 Heqs2.
          eapply monadic_fold_left_proper with
            (Ea:=repr_fold_eq m1 m2)
            (Eb:=mem_value_indt_same m1 m2).
          * typeclasses eauto.
          * typeclasses eauto.
          * assumption.
          * repeat split; [assumption|assumption|constructor].
          *
            intros x x' Ex.
            repeat break_let.
            destruct Ex as [E1 [E2 [E3 E4]]].
            subst.
            revert H0.
            apply Forall2_impl.
            intros a b H0.
            destruct fuel;[reflexivity|].
            specialize (H0 fuel z0 t t1 E2 capmeta1 capmeta2 Ecap).
            repeat break_match_goal; try assumption.
            inversion H0 as [H01 [H1 H2]].
            subst.
            repeat split; auto.
            apply eqlistA_length in H2.
            rewrite H2.
            reflexivity.
        +
          exfalso.
          cbn.
          cut(@serr_eq repr_fold_T (repr_fold_eq m1 m2) (inl s) (inr (t, t0, z, l)));
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold_T.
          rewrite <- Heqs1, <- Heqs0; clear Heqs1 Heqs0.
          eapply monadic_fold_left_proper with
            (Ea:=repr_fold_eq m1 m2)
            (Eb:=mem_value_indt_same m1 m2).
          * typeclasses eauto.
          * typeclasses eauto.
          * assumption.
          * repeat split; [assumption|assumption|constructor].
          *
            intros x x' Ex.
            repeat break_let.
            destruct Ex as [E1 [E2 [E3 E4]]].
            subst.
            revert H0.
            apply Forall2_impl.
            intros a b H0.
            destruct fuel;[reflexivity|].
            specialize (H0 fuel z1 t1 t3 E2 capmeta1 capmeta2 Ecap).
            repeat break_match_goal; try assumption.
            inversion H0 as [H01 [H1 H2]].
            subst.
            repeat split; auto.
            apply eqlistA_length in H2.
            rewrite H2.
            reflexivity.
        +
          exfalso.
          cbn.
          cut(@serr_eq repr_fold_T (repr_fold_eq m1 m2) (inr (t, t0, z, l)) (inl s));
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold_T.
          rewrite <- Heqs1, <- Heqs0; clear Heqs1 Heqs0.
          eapply monadic_fold_left_proper with
            (Ea:=repr_fold_eq m1 m2)
            (Eb:=mem_value_indt_same m1 m2).
          * typeclasses eauto.
          * typeclasses eauto.
          * assumption.
          * repeat split; [assumption|assumption|constructor].
          *
            intros x x' Ex.
            repeat break_let.
            destruct Ex as [E1 [E2 [E3 E4]]].
            subst.
            revert H0.
            apply Forall2_impl.
            intros a b H0.
            destruct fuel;[reflexivity|].
            specialize (H0 fuel z1 t1 t3 E2 capmeta1 capmeta2 Ecap).
            repeat break_match_goal; try assumption.
            inversion H0 as [H01 [H1 H2]].
            subst.
            repeat split; auto.
            apply eqlistA_length in H2.
            rewrite H2.
            reflexivity.
        +
          (* value case *)
          cbn.
          cut(@serr_eq repr_fold_T (repr_fold_eq m1 m2) ( inr (t1, t2, z0, l0)) (inr (t, t0, z, l))).
          {
            intros HS.
            invc HS.
            destruct H2 as [H2 [H3 H4]].
            repeat split ; [assumption|assumption|apply equlistA_concat_rev;assumption].
          }
          unfold repr_fold_T.
          rewrite <- Heqs, <- Heqs0; clear Heqs Heqs0.
          eapply monadic_fold_left_proper with
            (Ea:=repr_fold_eq m1 m2)
            (Eb:=mem_value_indt_same m1 m2).
          * typeclasses eauto.
          * typeclasses eauto.
          * assumption.
          * repeat split; [assumption|assumption|constructor].
          *
            intros x x' Ex.
            repeat break_let.
            destruct Ex as [E1 [E2 [E3 E4]]].
            subst.
            revert H0.
            apply Forall2_impl.
            intros a b H0.
            destruct fuel;[reflexivity|].
            specialize (H0 fuel z2 t3 t5 E2 capmeta1 capmeta2 Ecap).
            repeat break_match_goal; try assumption.
            inversion H0 as [H01 [H1 H2]].
            subst.
            repeat split; auto.
            apply eqlistA_length in H2.
            rewrite H2.
            reflexivity.
      -
        (* mval2 = MVstruct s l *)
        rewrite offsetof_same.
        break_match;[reflexivity|].
        clear Heqs.
        repeat break_let.
        break_match;[reflexivity|].
        clear Heqs.

        destruct_serr_eq ;  repeat break_match_hyp ; try inl_inr; repeat inl_inr_inv; subst.
        +
          (* Error case *)
          cut(@serr_eq repr_fold2_T (repr_fold2_eq m1 m2) (inl s) (inl s0));
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold2_T.
          rewrite <- Heqs1, <- Heqs2; clear Heqs1 Heqs2.

          eapply monadic_fold_left2_proper with
            (Ea:=repr_fold2_eq m1 m2)
            (Eb:=eq)
            (Ec:=struct_field_eq m1 m2); try typeclasses eauto;
            [reflexivity|assumption|repeat split;auto|].

          (* proper for 'f' *)
          intros a a' Ea.
          unfold repr_fold2_eq in Ea.
          repeat break_let.
          destruct Ea as [Ez [Efun1 [Ecap1 Ebytes]]].
          subst.
          apply list.Reflexive_instance_0.
          intros b.
          revert H1.
          repeat break_let.
          apply Forall2_impl.
          intros a b0 H.
          repeat break_let.
          destruct H as [II H].
          subst.
          destruct fuel;[reflexivity|].

          specialize (H fuel (addr2 + z1) t t1 Efun1 t0 t2 Ecap1).
          unfold serr_eq in H.
          Opaque CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
          repeat break_match_hyp;subst;try tauto.
          *
            reflexivity.
          *
            repeat break_let.
            break_match_goal.
            reflexivity.
            constructor.
            reflexivity.
            destruct H as [ H1 [H2 H3]].
            repeat split;auto.
            apply eqlistA_app.
            typeclasses eauto.
            auto.
            clear -H3.
            apply eqlistA_app;[typeclasses eauto | | assumption].
            apply list_init_proper.
            reflexivity.
            intros x y H.
            apply AbsByte_no_prov_eq.
            split; reflexivity.
            Transparent CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
        +
          exfalso.
          cut(@serr_eq repr_fold2_T (repr_fold2_eq m1 m2) (inl s) (inr (t, t0, z1, l0)));
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold2_T.
          rewrite <- Heqs0, <- Heqs1; clear Heqs0 Heqs1.
          eapply monadic_fold_left2_proper with
            (Ea:=repr_fold2_eq m1 m2)
            (Eb:=eq)
            (Ec:=struct_field_eq m1 m2);try typeclasses eauto;
            [reflexivity|assumption|repeat split;auto|].

          (* proper for 'f' *)
          intros a a' Ea.
          unfold repr_fold2_eq in Ea.
          repeat break_let.
          destruct Ea as [Ez [Efun1 [Ecap1 Ebytes]]].
          subst.
          apply list.Reflexive_instance_0.
          intros b.
          revert H1.
          repeat break_let.
          apply Forall2_impl.
          intros a b0 H.
          repeat break_let.
          destruct fuel;[reflexivity|].
          destruct H as [I H].
          subst i0.
          specialize (H fuel (addr2 + z2) _ _ Efun1 _ _ Ecap1).
          unfold serr_eq in H.
          Opaque CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
          repeat break_match_hyp;subst;try tauto.
          *
            cbn in Heqs0, Heqs1.
            reflexivity.
          *
            repeat break_let.
            break_match_goal.
            reflexivity.
            constructor.
            reflexivity.
            destruct H as [ H1 [H2 H3]].
            repeat split;auto.
            apply eqlistA_app.
            typeclasses eauto.
            auto.
            clear -H3.
            apply eqlistA_app;[typeclasses eauto | | assumption].
            apply list_init_proper.
            reflexivity.
            intros x y H.
            apply AbsByte_no_prov_eq.
            split; reflexivity.
            Transparent CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
        +
          exfalso;
            cut(@serr_eq repr_fold2_T (repr_fold2_eq m1 m2) (inr (t, t0, z1, l0)) (inl s) );
            [intros HS;invc HS;reflexivity|].
          unfold repr_fold2_T.
          rewrite <- Heqs0, <- Heqs1; clear Heqs0 Heqs1.
          eapply monadic_fold_left2_proper with
            (Ea:=repr_fold2_eq m1 m2)
            (Eb:=eq)
            (Ec:=struct_field_eq m1 m2);try typeclasses eauto;
            [reflexivity|assumption|repeat split;auto|].

          (* proper for 'f' *)
          intros a a' Ea.
          unfold repr_fold2_eq in Ea.
          repeat break_let.
          destruct Ea as [Ez [Efun1 [Ecap1 Ebytes]]].
          subst.
          apply list.Reflexive_instance_0.
          intros b.
          revert H1.
          repeat break_let.
          apply Forall2_impl.
          intros a b0 H.
          repeat break_let.
          destruct fuel;[reflexivity|].
          destruct H as [I H].
          subst i0.
          specialize (H fuel (addr2 + z2) _ _ Efun1 _ _ Ecap1).
          unfold serr_eq in H.
          Opaque CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
          repeat break_match_hyp;subst;try tauto.
          *
            reflexivity.
          *
            repeat break_let.
            break_match_goal.
            reflexivity.
            constructor.
            reflexivity.
            destruct H as [ H1 [H2 H3]].
            repeat split;auto.
            apply eqlistA_app.
            typeclasses eauto.
            auto.
            clear -H3.
            apply eqlistA_app;[typeclasses eauto | | assumption].
            apply list_init_proper.
            reflexivity.
            intros x y H.
            apply AbsByte_no_prov_eq.
            split; reflexivity.
            Transparent CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
        +
          (* value case *)
          cut(@serr_eq repr_fold2_T (repr_fold2_eq m1 m2) (inr (t1, t2, z2, l3)) (inr (t, t0, z1, l0))).
          {
            intros HS.
            destruct HS as [HS1 [HS2 [HS3 HS4]]].
            constructor.
            assumption.
            split.
            assumption.
            apply eqlistA_app.
            typeclasses eauto.
            assumption.
            apply list_init_proper.
            reflexivity.
            intros x y H.
            apply AbsByte_no_prov_eq.
            split; reflexivity.
          }

          unfold repr_fold2_T.
          rewrite <- Heqs, <- Heqs0; clear Heqs Heqs0.

          eapply monadic_fold_left2_proper with
            (Ea:=repr_fold2_eq m1 m2)
            (Eb:=eq)
            (Ec:=struct_field_eq m1 m2);try typeclasses eauto;
            [reflexivity|assumption|repeat split;auto|].

          (* proper for 'f' *)
          intros a a' Ea.
          unfold repr_fold2_eq in Ea.
          repeat break_let.
          destruct Ea as [Ez [Efun1 [Ecap1 Ebytes]]].
          subst.
          apply list.Reflexive_instance_0.
          intros b.
          revert H1.
          repeat break_let.
          apply Forall2_impl.
          intros a b0 H.
          repeat break_let.
          destruct fuel;[reflexivity|].

          destruct H as [I H].
          subst i0.
          specialize (H fuel (addr2 + z3) _ _ Efun1 _ _ Ecap1).
          unfold serr_eq in H.
          Opaque CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
          repeat break_match_hyp;subst;try tauto.
          *
            reflexivity.
          *
            repeat break_let.
            break_match_goal.
            reflexivity.
            constructor.
            reflexivity.
            destruct H as [ H1 [H2 H3]].
            repeat split;auto.
            apply eqlistA_app.
            typeclasses eauto.
            auto.
            clear -H3.
            apply eqlistA_app;[typeclasses eauto | | assumption].
            apply list_init_proper.
            reflexivity.
            intros x y H.
            apply AbsByte_no_prov_eq.
            split; reflexivity.
            Transparent CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.
      -
        (* mval2 = MVunion ... *)
        destruct H as [H0 [H1 H2]].
        subst.
        break_match;[reflexivity|].
        clear Heqs.

        destruct_serr_eq ;  repeat break_match_hyp ; try inl_inr; repeat inl_inr_inv; subst.
        +
          (* error case *)
          cbn.
          cut(@serr_eq repr_res_t (repr_res_eq m1 m2) (inl s) (inl s0));
            [intros HS;invc HS;reflexivity|].
          unfold repr_res_t.
          rewrite <- Heqs1, <- Heqs2.
          destruct fuel;[reflexivity|].
          eapply IHEmval; assumption.
        +
          exfalso.
          cut(@serr_eq repr_res_t (repr_res_eq m1 m2) (inl s) (inr (t, t0, l)));
            [intros HS;invc HS;reflexivity|].
          unfold repr_res_t.
          rewrite <- Heqs0, <- Heqs1.
          destruct fuel;[reflexivity|].
          eapply IHEmval; assumption.
        +
          exfalso.
          cut(@serr_eq repr_res_t (repr_res_eq m1 m2) (inr (t, t0, l)) (inl s));
            [intros HS;invc HS;reflexivity|].
          unfold repr_res_t.
          rewrite <- Heqs0, <- Heqs1.
          destruct fuel;[reflexivity|].
          eapply IHEmval; assumption.
        +
          (* value case *)
          cut(@serr_eq repr_res_t (repr_res_eq m1 m2) (inr (t1, t2, l0)) (inr (t, t0, l))).
          {
            intros HS.
            invc HS. destruct H0.
            cbn; repeat split; try reflexivity; try assumption.
            apply eqlistA_app.
            typeclasses eauto.
            assumption.
            apply list_init_proper.
            apply eqlistA_length in H1.
            rewrite H1. reflexivity.
            intros x y E.
            subst.
            repeat split; auto.
          }
          unfold repr_res_t.
          rewrite <- Heqs, <- Heqs0.
          destruct fuel;[reflexivity|].
          eapply IHEmval; assumption.
    Qed.
 *)
    Admitted.

  End repr_same_proof.
  Opaque CheriMemoryWithPNVI.repr CheriMemoryWithoutPNVI.repr.

  (* --- Stateful proofs below --- *)

  Definition lift_sum2
    {A1 A2 B1 B2 C:Type}
    (fl: A1->A2->C) (fr:B1->B2->C)
    (default: C)
    (a:sum A1 B1) (b:sum A2 B2): C :=
    match a,b with
    | inl l1, inl l2 => fl l1 l2
    | inr r1, inr r2 => fr r1 r2
    | _, _ => default
    end.

  Lemma init_ghost_tags_same:
    forall (sz : Z) (addr : AddressValue.t) (c1 c0 : ZMap.t (bool * CapGhostState)),
      ZMap.Equal (elt:=bool * CapGhostState) c0 c1 ->
      ZMap.Equal (elt:=bool * CapGhostState)
        (CheriMemoryWithPNVI.init_ghost_tags addr sz c0)
        (CheriMemoryWithoutPNVI.init_ghost_tags addr sz c1).
  Proof.
    unfold CheriMemoryWithPNVI.init_ghost_tags, CheriMemoryWithoutPNVI.init_ghost_tags.
    generalize (alignof_pointer MorelloImpl.get) as al.
    generalize ((false, {| tag_unspecified := true; bounds_unspecified := false |})) as v.
    intros v al sz addr c1 c0 E k.
    repeat break_let.
    setoid_rewrite E.
    reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.init_ghost_tags CheriMemoryWithoutPNVI.init_ghost_tags.

  Lemma AddressValue_Z_id:
    forall a,
      AddressValue.of_Z (AddressValue.to_Z a) = a.
  Proof.
    intros a.
    unfold AddressValue.t, AddressValue.of_Z, AddressValue.to_Z in *.
    unfold bv_to_Z_unsigned.
    apply bitvector.Z_to_bv_bv_unsigned.
  Qed.

  Class SameValue {T1 T2:Type}
    (R: T1 -> T2 -> Prop) (* relation between values *)
    (M1: CheriMemoryWithPNVI.memM T1)
    (M2: CheriMemoryWithoutPNVI.memM T2) : Prop
    :=
    eval_to_same : forall mem_state1 mem_state2,
        mem_state_same mem_state1 mem_state2 ->
        lift_sum2 eq R False
          (evalErrS M1 mem_state1)
          (evalErrS M2 mem_state2).

  Class SameState {T1 T2:Type}
    (M1: CheriMemoryWithPNVI.memM T1)
    (M2: CheriMemoryWithoutPNVI.memM T2) : Prop
    :=
    exec_to_same : forall mem_state1 mem_state2,
        mem_state_same mem_state1 mem_state2 ->
        lift_sum2 eq mem_state_same False
          (execErrS M1 mem_state1)
          (execErrS M2 mem_state2).

  Class Same {T1 T2:Type}
    (R: T1 -> T2 -> Prop) (* relation between values *)
    (M1: CheriMemoryWithPNVI.memM T1)
    (M2: CheriMemoryWithoutPNVI.memM T2) : Prop
    := {
      Same_Value :: SameValue R M1 M2 ;
      Same_State :: SameState M1 M2 ;
    }.

  Lemma ret_Same {T1 T2:Type}
    {R: T1 -> T2 -> Prop} (* relation between values *)
    :
    forall x1 x2, R x1 x2 -> Same R (ret x1) (ret x2).
  Proof.
    intros x1 x2 E.
    repeat break_match;
      unfold CheriMemoryWithPNVI.memM, CheriMemoryWithoutPNVI.memM,
      CheriMemoryWithPNVI.mem_state, CheriMemoryWithoutPNVI.mem_state.
    split; intros m1 m2 M;cbn;try reflexivity; try assumption.
  Qed.

  Lemma raise_Same_eq {T:Type}:
    forall x1 x2, x1 = x2 ->
                  @Same T T (@eq T)
                    (@raise memMError (errS CheriMemoryWithPNVI.mem_state_r memMError)
                       (Exception_errS CheriMemoryWithPNVI.mem_state_r memMError) T
                       x1)
                    (@raise memMError (errS CheriMemoryWithoutPNVI.mem_state_r memMError)
                       (Exception_errS CheriMemoryWithoutPNVI.mem_state_r memMError) T
                       x2).
  Proof.
    intros x1 x2 E.
    repeat break_match;
      unfold CheriMemoryWithPNVI.memM, CheriMemoryWithoutPNVI.memM,
      CheriMemoryWithPNVI.mem_state, CheriMemoryWithoutPNVI.mem_state.
    split; intros m1 m2 M;cbn;try reflexivity; try assumption.
  Qed.

  Instance fail_same {T:Type}:
    forall l1 l2 e1 e2, l1 = l2 /\ e1 = e2 ->

                        @Same T T (@eq T)
                          (CheriMemoryWithPNVI.fail l1 e1)
                          (CheriMemoryWithoutPNVI.fail l2 e2).
  Proof.
    intros l1 l2 e1 e2 [EL EE].
    subst.
    unfold CheriMemoryWithPNVI.fail, CheriMemoryWithoutPNVI.fail.
    break_match;
      apply raise_Same_eq;reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.fail CheriMemoryWithoutPNVI.fail.

  Instance fail_noloc_same {T:Type}:
    forall e1 e2, e1 = e2 ->
                  @Same T T (@eq T)
                    (CheriMemoryWithPNVI.fail_noloc e1)
                    (CheriMemoryWithoutPNVI.fail_noloc e2).
  Proof.
    intros e1 e2 EE.
    subst.
    unfold CheriMemoryWithPNVI.fail_noloc, CheriMemoryWithoutPNVI.fail_noloc.
    apply fail_same.
    split;
      reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.fail_noloc CheriMemoryWithoutPNVI.fail_noloc.

  Lemma bind_Same {T1 T2 T1' T2':Type}
    (R: T1 -> T2 -> Prop) (* relation between values *)
    (R': T1' -> T2' -> Prop) (* relation between values *)
    {M1: CheriMemoryWithPNVI.memM T1'}
    {M2: CheriMemoryWithoutPNVI.memM T2'}
    {C1: T1' -> CheriMemoryWithPNVI.memM T1}
    {C2: T2' -> CheriMemoryWithoutPNVI.memM T2}
    :
    (Same R' M1 M2 /\
       (forall x1 x2, R' x1 x2 -> Same R (C1 x1) (C2 x2)))
    ->
      Same R (bind M1 C1) (bind M2 C2).
  Proof.
    intros [[EMV EMS] EC].
    split;
      intros m1 m2 M;
      unfold lift_sum2;
      unfold execErrS, evalErrS;
      repeat break_let;
      unfold SameValue in EMV;
      repeat break_match; invc Heqs1; invc Heqs0;

      cbn in *;
      repeat break_let;
      destruct s,s0; try tuple_inversion;

      specialize (EMV m1 m2 M);
      unfold lift_sum2, evalErrS in EMV;
      repeat break_let;
      repeat break_match;
      repeat tuple_inversion;
      repeat inl_inr_inv; subst; try reflexivity; try inl_inr; try tauto;

      specialize (EMS m1 m2 M);
      unfold lift_sum2, execErrS in EMS;
      repeat break_let;
      repeat break_match;
      repeat tuple_inversion;
      repeat inl_inr_inv; subst; try reflexivity; try inl_inr; try tauto;


      match goal with
      | [H1: C1 ?T1 ?M1 = _, H2: C2 ?T2 ?M2 = _,  H3: mem_state_same ?M1 ?M2 |- _ ] =>
          specialize (EC T1 T2 EMV);
          destruct EC as [ECV ECS];
          specialize (ECV M1 M2 EMS);
          unfold lift_sum2, evalErrS in ECV;
          repeat break_let;
          repeat break_match;
          repeat tuple_inversion;
          repeat inl_inr_inv; subst; try reflexivity; try inl_inr; try tauto
      end.


    specialize (ECS m7 m8 EMS).
    unfold lift_sum2, execErrS in ECS.
    repeat break_let;
      repeat break_match;
      repeat tuple_inversion;
      repeat inl_inr_inv; subst; try reflexivity; try inl_inr; try tauto.
  Qed.

  (* special case of [bind_Same] *)
  Lemma bind_Same_eq {T1 T2 T:Type}
    {R: T1 -> T2 -> Prop} (* relation between values *)
    {M1: CheriMemoryWithPNVI.memM T}
    {M2: CheriMemoryWithoutPNVI.memM T}
    {C1: T -> CheriMemoryWithPNVI.memM T1}
    {C2: T -> CheriMemoryWithoutPNVI.memM T2}
    :
    (Same eq M1 M2 /\
       (forall x1 x2, x1 = x2 -> Same R (C1 x1) (C2 x2)))
    ->
      Same R (bind M1 C1) (bind M2 C2).
  Proof.
    apply bind_Same.
  Qed.

  Lemma put_Same
    {V1:CheriMemoryWithPNVI.mem_state_r}
    {V2:CheriMemoryWithoutPNVI.mem_state_r}
    :
    mem_state_same V1 V2 ->
    Same (@eq unit) (put V1) (put V2).
  Proof.
    split.
    -
      split.
    -
      destruct_mem_state_same H.
      intros m1 m2 M;
        destruct_mem_state_same M.
      repeat split;try assumption;destruct Mvarargs as [Mvarargs1 Mvarargs2];
        try apply Mvarargs1; try apply Mvarargs2.

      1,2: apply Mbytes.
      1,2: destruct Mbytes as [Mbytes1 Mbytes2];
      specialize (Mbytes2 k _ _ H H0);
      invc Mbytes2;
      destruct H1;
      assumption.
  Qed.

  Lemma update_Same
    {F1:CheriMemoryWithPNVI.mem_state_r -> CheriMemoryWithPNVI.mem_state_r}
    {F2:CheriMemoryWithoutPNVI.mem_state_r -> CheriMemoryWithoutPNVI.mem_state_r}
    :

    (forall m1 m2, mem_state_same m1 m2 ->  mem_state_same (F1 m1) (F2 m2)) ->
    Same (@eq unit) (ErrorWithState.update F1) (ErrorWithState.update F2).
  Proof.
    split.
    -
      split.
    -
      intros m1 m2 M.
      specialize (H m1 m2 M).
      destruct_mem_state_same H.
      repeat split;try assumption;destruct Mvarargs as [Mvarargs1 Mvarargs2];
        try apply Mvarargs1; try apply Mvarargs2.

      1,2: apply Mbytes.
      1,2: destruct Mbytes as [Mbytes1 Mbytes2];
      specialize (Mbytes2 k _ _ H H0);
      invc Mbytes2;
      destruct H1;
      assumption.
  Qed.

  Lemma serr2InternalErr_same
    {T: Type}
    (R: relation T)
    {M1 M2: serr T}:
    serr_eq R M1 M2 ->
    Same R
      (CheriMemoryWithPNVI.serr2InternalErr M1)
      (CheriMemoryWithoutPNVI.serr2InternalErr M2).
  Proof.
    intros H.
    unfold serr_eq in H.
    unfold CheriMemoryWithPNVI.serr2InternalErr, CheriMemoryWithoutPNVI.serr2InternalErr.
    repeat break_match;subst.
    -
      split.
      + unfold SameValue; reflexivity.
      + unfold SameState; reflexivity.
    - tauto.
    - tauto.
    - split.
      + unfold SameValue.
        intros mem_state1 mem_state2 H0.
        unfold lift_sum2.
        assumption.
      + unfold SameState.
        intros mem_state1 mem_state2 H0.
        unfold lift_sum2.
        assumption.
  Qed.

  Lemma serr2InternalErr_same_eq {T: Type}
    {M1 M2: serr T}:
    M1 = M2 ->
    Same (@eq T)
      (CheriMemoryWithPNVI.serr2InternalErr M1)
      (CheriMemoryWithoutPNVI.serr2InternalErr M2).
  Proof.
    intros.
    apply serr2InternalErr_same.
    rewrite H. clear H.
    unfold serr_eq.
    break_match;reflexivity.
  Qed.

  Lemma get_Same:
    @Same CheriMemoryWithPNVI.mem_state_r CheriMemoryWithoutPNVI.mem_state_r
      mem_state_same
      (@get CheriMemoryWithPNVI.mem_state_r CheriMemoryWithPNVI.memM
         (State_errS CheriMemoryWithPNVI.mem_state memMError))
      (@get CheriMemoryWithoutPNVI.mem_state_r CheriMemoryWithoutPNVI.memM
         (State_errS CheriMemoryWithoutPNVI.mem_state memMError)).
  Proof.
    split;
      intros m1 m2 M;
      destruct_mem_state_same M;
      repeat split;try assumption;destruct Mvarargs as [Mvarargs1 Mvarargs2];
      try apply Mvarargs1; try apply Mvarargs2.

    1,2,5,6: apply Mbytes.
    all: destruct Mbytes as [Mbytes1 Mbytes2];
      specialize (Mbytes2 k _ _ H H0);
      invc Mbytes2;
      destruct H1;
      assumption.
  Qed.

  (* special case of [lift_sum2] where the type is the same and relations are both [eq] *)
  Lemma lift_sum2_eq_eq
    {T:Type}
    (M1: CheriMemoryWithPNVI.memM T)
    (M2: CheriMemoryWithoutPNVI.memM T):
    forall mem_state1 mem_state2,
      lift_sum2 eq eq False
        (evalErrS M1 mem_state1)
        (evalErrS M2 mem_state2) <->
        eq (evalErrS M1 mem_state1) (evalErrS M2 mem_state2).
  Proof.
    intros mem_state1 mem_state2.
    split.
    -
      unfold lift_sum2.
      repeat break_match; intros H; try contradiction;
        try (rewrite H; reflexivity).
    -
      intros E.
      rewrite E.
      unfold lift_sum2.
      repeat break_match; try contradiction; reflexivity.
  Qed.

  Ltac same_step
    :=
    match goal with
    |[|- Same eq (bind _ _) (bind _ _)] => apply bind_Same_eq
    |[|- Same eq (raise _) (raise _)] => apply raise_Same_eq
    |[|- Same _ (ret _) (ret _)] => apply ret_Same
    |[|- Same _ get get] => apply get_Same
    |[|- Same eq (put _) (put _)] => apply put_Same
    |[|- Same eq (ErrorWithState.update _) (ErrorWithState.update _)] => apply update_Same
    end.


  Section allocator_proofs.

  (*
    Variable  size : Z.
    Variable  align : Z.

    (* Temporary make these transparent as we have proven some of the lemmas by brute force before introducing [fail_same] and [fail_noloc_same] *)
    Transparent CheriMemoryWithPNVI.fail_noloc CheriMemoryWithoutPNVI.fail_noloc CheriMemoryWithPNVI.fail CheriMemoryWithoutPNVI.fail.

    Instance allocator_same_result:
      SameValue eq (CheriMemoryWithPNVI.allocator size align) (CheriMemoryWithoutPNVI.allocator size align).
    Proof.
      intros mem_state1 mem_state2 M.
      destruct_mem_state_same M.
      (* return value *)
      unfold evalErrS.
      unfold CheriMemoryWithPNVI.allocator, CheriMemoryWithoutPNVI.allocator.
      unfold put, ret, bind.
      cbn.
      repeat break_let.
      unfold CheriMemoryWithPNVI.memM in *.
      unfold CheriMemoryWithPNVI.mem_state in *.
      repeat break_match; repeat break_match;
        repeat tuple_inversion;
        rewrite Mlastaddr in *; try congruence; try reflexivity.
      -
        rewrite <- Malloc_id in *.
        rewrite  Heqp1 in Heqp4.
        tuple_inversion.
        reflexivity.
      -
        rewrite <- Malloc_id in *.
        rewrite  Heqp1 in Heqp4.
        tuple_inversion.
        reflexivity.
    Qed.

    Instance allocator_same_state:
      SameState (CheriMemoryWithPNVI.allocator size align) (CheriMemoryWithoutPNVI.allocator size align).
    Proof.
      intros mem_state1 mem_state2 M.
      destruct_mem_state_same M.
      unfold lift_sum2.
      unfold CheriMemoryWithPNVI.mem_state in *.
      unfold execErrS.
      repeat break_let.
      repeat break_match;invc Heqs1;invc Heqs0.
      all: cbn_hyp Heqp; cbn_hyp Heqp0; repeat break_let.
      +
        repeat break_match_hyp;
          repeat tuple_inversion; auto.
      +
        repeat break_match_hyp;
          repeat tuple_inversion;
          (rewrite Mlastaddr in Heqb1, Heqp4;
           rewrite Heqp4 in Heqp2;
           tuple_inversion;
           congruence).
      +
        repeat break_match_hyp;
          repeat tuple_inversion;
          (rewrite Mlastaddr in Heqb1, Heqp4;
           rewrite Heqp4 in Heqp2;
           tuple_inversion;
           congruence).
      +
        (* main proof here: [mem_state_same m1 m2] *)
        repeat break_match_hyp;
          repeat tuple_inversion;
          unfold mem_state_same; cbn;
          (try rewrite Malloc_id in *; clear Malloc_id;
           try rewrite Mnextiota in *; clear Mnextiota;
           try rewrite Mlastaddr in *; clear Mlastaddr;
           try rewrite Mnextvararg in *; clear Mnextvararg);
          rewrite Heqp4 in Heqp2; tuple_inversion;
          repeat split; auto.

        all: destruct Mvarargs as [MvarargsIn MvarargsMap].
        all: auto.
        all: try apply MvarargsIn.
        all: try find_contradiction.
        1,2,6,7: apply Mbytes.
        1,2,4,5:
          destruct Mbytes as [Mbytes1 Mbytes2];
        specialize (Mbytes2 k _ _ H H0);
        invc Mbytes2;
        destruct H1;
        assumption.
        1,2: apply init_ghost_tags_same; assumption.
    Qed.

    Instance allocator_same:
      Same eq (CheriMemoryWithPNVI.allocator size align) (CheriMemoryWithoutPNVI.allocator size align).
    Proof.
      split;typeclasses eauto.
    Qed.
    Opaque CheriMemoryWithPNVI.allocator CheriMemoryWithoutPNVI.allocator.
 *)
  End allocator_proofs.

   (*
  Lemma num_of_int_same:
    forall x, CheriMemoryWithPNVI.num_of_int x = CheriMemoryWithoutPNVI.num_of_int x.
  Proof.
    auto.
  Qed.
  Opaque CheriMemoryWithPNVI.num_of_int CheriMemoryWithoutPNVI.num_of_int.

  Instance allocate_region_same:
    forall tid pref align_int size_int,
      Same pointer_value_eq
        (CheriMemoryWithPNVI.allocate_region tid pref align_int size_int)
        (CheriMemoryWithoutPNVI.allocate_region tid pref align_int size_int).
  Proof.
    intros tid pref align_int size_int.

    unfold CheriMemoryWithPNVI.allocate_region, CheriMemoryWithoutPNVI.allocate_region.
    apply bind_Same_eq.
    split.
    apply allocator_same.
    intros x1 x2 H.
    repeat break_let.
    apply bind_Same_eq.
    split.
    -
      same_step.
      intros m1 m2 H0.
      destruct_mem_state_same H0.
      repeat split;cbn;try assumption;
        (try setoid_rewrite Mallocs0; try reflexivity);
        destruct Mvarargs as [Mvarargs01 Mvarargs02];
        try apply Mvarargs01;
        try apply Mvarargs02.
      2,3: apply Mbytes.
      2,3: destruct Mbytes as [Mbytes1 Mbytes2];
      cbn in H0; cbn in H1;
      specialize (Mbytes2 k _ _ H0 H1);
      invc Mbytes2;
      destruct H2;
      assumption.
      apply add_m;tuple_inversion;auto.
    -
      intros x0 x3 H0.
      same_step.
      constructor.
      rewrite num_of_int_same.
      tuple_inversion.
      reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.allocate_region CheriMemoryWithoutPNVI.allocate_region.

    Opaque CheriMemoryWithPNVI.fail_noloc CheriMemoryWithoutPNVI.fail_noloc CheriMemoryWithPNVI.fail CheriMemoryWithoutPNVI.fail.

  Definition Z_AbsByte_eq (za1: (Z*AbsByte)) (za2: (Z*AbsByte)): Prop
    :=
    let '(z1,a1) := za1 in
    let '(z2,a2) := za2 in
    z1 = z2 /\ AbsByte_eq a1 a2.

  Instance Z_AbsByte_Equivalence: Equivalence Z_AbsByte_eq.
  Proof.
    split.
    -
      intros a.
      destruct a.
      constructor; reflexivity.
    -
      intros a b.
      destruct a, b.
      intros [H1 H2].
      constructor.
      auto.
      symmetry.
      auto.
    -
      intros a b c.
      destruct a, b, c.
      intros [H1 H2].
      intros [H3 H4].
      constructor.
      rewrite H1. apply H3.
      rewrite H2. apply H4.
  Qed.

  Section allocate_object_proofs.
    Variable  tid : MemCommonExe.thread_id.
    Variable  pref : CoqSymbol.prefix.
    Variable  int_val: CheriMemoryWithPNVI.integer_value.
    Variable  ty : CoqCtype.ctype.
    Variable  init_opt : option CheriMemoryWithPNVI.mem_value.

    Instance allocate_object_same:
      Same pointer_value_eq
        (CheriMemoryWithPNVI.allocate_object tid pref int_val ty init_opt)
        (CheriMemoryWithoutPNVI.allocate_object tid pref int_val ty init_opt).
    Proof.

      unfold CheriMemoryWithPNVI.allocate_object, WithPNVISwitches.get_switches, CheriMemoryWithPNVI.DEFAULT_FUEL.
      unfold CheriMemoryWithoutPNVI.allocate_object, WithoutPNVISwitches.get_switches, CheriMemoryWithoutPNVI.DEFAULT_FUEL.

      apply bind_Same_eq.
      split.
      apply serr2InternalErr_same_eq.
      rewrite sizeof_same.
      reflexivity.
      intros;subst;try break_let.

      apply bind_Same_eq.
      split.
      apply allocator_same.
      intros;subst;try break_let.

      apply bind_Same_eq.
      split.
      break_match.
      -
        apply bind_Same with (R':=mem_state_same).
        split.
        same_step.
        intros.
        apply bind_Same with (R':=repr_res_eq).
        split.
        {
          apply serr2InternalErr_same with (R:=repr_res_eq).
          destruct_mem_state_same H.
          apply repr_same.
          repeat split; try assumption.
          reflexivity.
        }
        intros; repeat break_let.
        apply bind_Same_eq.
        split.
        same_step.
        {
          destruct_mem_state_same H.
          destruct H0 as [H0 [H1 H2]].
          subst.
          repeat split;try assumption;
            destruct Mvarargs as [Mvarargs1 Mvarargs2];try apply Mvarargs1; try apply Mvarargs2.

          - cbn;apply add_m;[reflexivity|reflexivity| assumption].
          - apply In_m_Proper_Equiv with (R:=AbsByte_eq);[reflexivity|].
            apply List_fold_left_proper with (Eb:=Z_AbsByte_eq); try reflexivity; try typeclasses eauto; try assumption.
            + intros l1 l2 LE a1 a2 AE.
              repeat break_let.
              cbn in AE.
              destruct AE.
              subst.
              rewrite LE.
              rewrite H3.
              reflexivity.
            + apply list_mapi_Proper with (pA:=AbsByte_eq) (pB:=Z_AbsByte_eq).
              *
                intros n a1 a2 AE.
                constructor.
                reflexivity.
                assumption.
              * symmetry;apply H2.
            + symmetry; assumption.
          - apply In_m_Proper_Equiv with (R:=AbsByte_eq);[reflexivity|].
            apply List_fold_left_proper with (Eb:=Z_AbsByte_eq); try reflexivity; try typeclasses eauto; try assumption.
            + intros l1 l2 LE a1 a2 AE.
              repeat break_let.
              cbn in AE.
              destruct AE.
              subst.
              rewrite LE.
              rewrite H3.
              reflexivity.
            + apply list_mapi_Proper with (pA:=AbsByte_eq) (pB:=Z_AbsByte_eq).
              *
                intros n a1 a2 AE.
                constructor.
                reflexivity.
                assumption.
              * apply H2.
          -
            cbn in H, H3.
            cut(AbsByte_eq e e').
            {
              intros A.
              clear -A.
              invc A.
              apply H.
            }
            match goal with
            | [H0: ZMap.MapsTo k e ?L1,
                  H1: ZMap.MapsTo k e' ?L2 |- _] =>
                cut(ZMap.Equiv AbsByte_eq L1 L2)
            end.
            {
              intros E.
              clear -H H3 E.
              destruct E as [_ E].
              eapply E.
              eapply H.
              eapply H3.
            }

            apply List_fold_left_proper with (Eb:=Z_AbsByte_eq); try reflexivity; try typeclasses eauto; try assumption.
            + intros l1 l2 LE a1 a2 AE.
              repeat break_let.
              cbn in AE.
              destruct AE.
              subst.
              rewrite LE.
              rewrite H5.
              reflexivity.
            + apply list_mapi_Proper with (pA:=AbsByte_eq) (pB:=Z_AbsByte_eq).
              * intros n a1 a2 AE.
                constructor.
                reflexivity.
                assumption.
              * apply H2.
          -
            (* copy-paste from previous goal! *)
            cbn in H, H3.
            cut(AbsByte_eq e e').
            {
              intros A.
              clear -A.
              invc A.
              apply H.
            }
            match goal with
            | [H0: ZMap.MapsTo k e ?L1,
                  H1: ZMap.MapsTo k e' ?L2 |- _] =>
                cut(ZMap.Equiv AbsByte_eq L1 L2)
            end.
            {
              intros E.
              clear -H H3 E.
              destruct E as [_ E].
              eapply E.
              eapply H.
              eapply H3.
            }

            apply List_fold_left_proper with (Eb:=Z_AbsByte_eq); try reflexivity; try typeclasses eauto; try assumption.
            + intros l1 l2 LE a1 a2 AE.
              repeat break_let.
              cbn in AE.
              destruct AE.
              subst.
              rewrite LE.
              rewrite H5.
              reflexivity.
            + apply list_mapi_Proper with (pA:=AbsByte_eq) (pB:=Z_AbsByte_eq).
              * intros n a1 a2 AE.
                constructor.
                reflexivity.
                assumption.
              * apply H2.
        }
        intros.
        same_step;reflexivity.
      -
        apply bind_Same_eq.
        split.
        same_step.
        {
          intros m1 m2 H.
          destruct_mem_state_same H.
          repeat split;try assumption;
            destruct Mvarargs as [Mvarargs1 Mvarargs2];try apply Mvarargs1; try apply Mvarargs2.
          - cbn;apply add_m;[reflexivity|reflexivity| assumption].
          - cbn; apply Mbytes.
          - cbn; apply Mbytes.
          -
            cut(AbsByte_eq e e').
            {
              intros A.
              invc A.
              apply H1.
            }
            destruct Mbytes as [_ E].
            eapply E;[eapply H|eapply H0].
          -
            cut(AbsByte_eq e e').
            {
              intros A.
              invc A.
              apply H1.
            }
            destruct Mbytes as [_ E].
            eapply E;[eapply H|eapply H0].
        }
        intros.
        same_step;reflexivity.
      -
        intros;subst;try break_let.
        same_step.
        constructor.
        reflexivity.
    Qed.
    Opaque CheriMemoryWithPNVI.allocate_object CheriMemoryWithoutPNVI.allocate_object.

  End allocate_object_proofs.

  Instance find_live_allocation_same (addr:AddressValue.t):
    Same eq
      (CheriMemoryWithPNVI.find_live_allocation addr)
      (CheriMemoryWithoutPNVI.find_live_allocation addr).
  Proof.
    unfold CheriMemoryWithPNVI.find_live_allocation, CheriMemoryWithoutPNVI.find_live_allocation.
    apply bind_Same with (R':=mem_state_same).
    split.
    same_step.
    intros x1 x2 H.
    same_step.
    destruct H as [_ [_ [_ [H4 _]]]].
    apply zmap_fold_proper with (Eelt:=eq);auto.
    intros x x' Ex a a' Ea y y' Ey.
    subst.
    break_match;reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.find_live_allocation CheriMemoryWithoutPNVI.find_live_allocation.

  Definition abst_res_eq: relation (taint_indt * mem_value_with_err * list AbsByte)
    := fun '(t1,mv1,b1) '(t2,mv2,b2) =>
         t1 = t2 /\ mem_value_with_err_same mv1 mv2 /\ eqlistA AbsByte_eq b1 b2.

  Theorem abst_same
    (fuel: nat)
    (find_overlapping1 : Z -> CheriMemoryWithPNVI.overlap_indt)
    (find_overlapping2 : Z -> CheriMemoryWithoutPNVI.overlap_indt)
    (funptrmap1 funptrmap2 : ZMap.t (digest * string * Capability_GS.t))
    (tag_query_f : Z -> (bool* CapGhostState))
    (addr : Z)
    (cty : CoqCtype.ctype)
    (bs1 bs2 : list AbsByte)
    :
    ZMap.Equal funptrmap1 funptrmap2 ->
    eqlistA AbsByte_eq bs1 bs2 ->
    serr_eq abst_res_eq
      (CheriMemoryWithPNVI.abst fuel find_overlapping1 funptrmap1 tag_query_f addr cty bs1)
      (CheriMemoryWithoutPNVI.abst fuel find_overlapping2 funptrmap2 tag_query_f addr cty bs2).
  Proof.
  Admitted.
  Opaque CheriMemoryWithPNVI.abst CheriMemoryWithoutPNVI.abst.

  Lemma fetch_bytes_same:
    forall (bytemap1 bytemap2 : ZMap.t AbsByte)
      (base_addr : Z)
      (n_bytes : Z),
      ZMap.Equiv AbsByte_eq bytemap1 bytemap2 ->
      eqlistA AbsByte_eq
        (CheriMemoryWithPNVI.fetch_bytes bytemap1 base_addr n_bytes)
        (CheriMemoryWithoutPNVI.fetch_bytes bytemap2 base_addr n_bytes).
  Proof.
    intros bytemap1 bytemap2 base_addr n_bytes B.
    unfold CheriMemoryWithPNVI.fetch_bytes, CheriMemoryWithoutPNVI.fetch_bytes.
    apply list_map_Proper with (pA:=eq).
    -
      intros x y E.
      subst y. rename x into k.
      unfold ZMap.Equiv in B.
      destruct B as [B1 B2].
      break_match;break_match.
      +
        apply B2 with (k:=k);
        apply find_mapsto_iff; assumption.
      +
        exfalso.
        apply not_find_in_iff in Heqo0.
        destruct Heqo0.
        apply B1.
        apply in_find_iff.
        rewrite Heqo.
        auto.
      +
        exfalso.
        apply not_find_in_iff in Heqo.
        destruct Heqo.
        apply B1.
        apply in_find_iff.
        rewrite Heqo0.
        auto.
      +
        unfold CheriMemoryWithPNVI.PNVI_prov, CheriMemoryWithoutPNVI.PNVI_prov.
        rewrite has_PNVI_WithPNVI, has_PNVI_WithoutPNVI.
        constructor.
        split; auto.
    -
      apply list_init_proper;auto.
      intros x y E.
      subst.
      reflexivity.
  Qed.
  Opaque CheriMemoryWithPNVI.fetch_bytes CheriMemoryWithoutPNVI.fetch_bytes.

  Lemma maybe_revoke_pointer_same:
    forall
      (alloc_base alloc_limit: Z)
      (st1: CheriMemoryWithPNVI.mem_state)
      (st2: CheriMemoryWithoutPNVI.mem_state)
      (addr1 addr2: Z)
      (meta1 meta2: (bool*CapGhostState)),

      addr1 = addr2 ->
      meta1 = meta2 ->
      mem_state_same st1 st2 ->
      Same eq (CheriMemoryWithPNVI.maybe_revoke_pointer alloc_base alloc_limit st1 addr1 meta1)
        (CheriMemoryWithoutPNVI.maybe_revoke_pointer alloc_base alloc_limit st2 addr2 meta2).
  Proof.
    intros alloc_base alloc_limit st1 st2 addr1 addr2 meta1 meta2 H1 H2 M.
    subst.
    unfold CheriMemoryWithPNVI.maybe_revoke_pointer, CheriMemoryWithoutPNVI.maybe_revoke_pointer.
    break_match.
    -
      same_step; reflexivity.
    -
      apply bind_Same with (R':=abst_res_eq).
      split.
      +
        apply serr2InternalErr_same.
        apply abst_same.
        apply M.
        apply fetch_bytes_same.
        apply M.
      +
        intros x1 x2 H.
        repeat break_let.
        destruct H as [Ht [Hm Hl]].
        subst.
        destruct m,m0; invc Hm; try (apply raise_Same_eq;reflexivity).
        destruct H0 as [Hc Hp].
        subst.
        invc Hp.
        break_match.
        apply raise_Same_eq; reflexivity.
        break_match;
        apply ret_Same;reflexivity.
  Qed.

  Lemma zmap_mmapi_same:
    forall (A B:Type) (R: relation B) f1 f2 (m1 m2:ZMap.t A),
      ZMap.Equal m1 m2 ->
      (forall k1 k2 v1 v2, k1=k2 -> v1=v2 -> Same R (f1 k1 v1) (f2 k2 v2)) ->
      Same ZMap.Equal
        (zmap_mmapi f1 m1)
        (zmap_mmapi f2 m2).
  Proof.
    intros A B R f1 f2 m1 m2 H H0.
    split.
    -
      unfold zmap_mmapi.
  Admitted.

  Lemma revoke_pointers_same:
    forall a : allocation,
      Same eq (CheriMemoryWithPNVI.revoke_pointers a)
        (CheriMemoryWithoutPNVI.revoke_pointers a).
  Proof.
    intros a.
    unfold CheriMemoryWithPNVI.revoke_pointers, CheriMemoryWithoutPNVI.revoke_pointers.
    eapply bind_Same with (R':=mem_state_same).
    split.
    same_step.
    intros x1 x2 H.
    eapply bind_Same with (R':=ZMap.Equal).
    split.
    -
      eapply zmap_mmapi_same.
      apply H.
      intros k1 k2 v1 v2 H0 H1.
      apply maybe_revoke_pointer_same; auto.
    -
      intros x0 x3 H0.
      apply update_Same.
      intros m1 m2 H1.
      unfold CheriMemoryWithPNVI.mem_state_with_capmeta, CheriMemoryWithoutPNVI.mem_state_with_capmeta.
      destruct_mem_state_same H.
      destruct_mem_state_same H1.

      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      split;[cbn;auto|].
      cbn.
      auto.
  Qed.

  Lemma remove_allocation_same:
    forall z : Z,
      Same eq (CheriMemoryWithPNVI.remove_allocation z)
        (CheriMemoryWithoutPNVI.remove_allocation z).
  Proof.
    intros z.
    unfold CheriMemoryWithPNVI.remove_allocation, CheriMemoryWithoutPNVI.remove_allocation.
    same_step.
    intros m1 m2 H.
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    split.
    apply remove_m_Proper;[reflexivity|apply H].
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    split;[cbn; apply H|].
    cbn.
    apply H.
  Qed.

  Lemma get_allocation_same:
    forall s1 s2 : storage_instance_id,
      s1 = s2 ->
      Same eq (CheriMemoryWithPNVI.get_allocation s1) (CheriMemoryWithoutPNVI.get_allocation s2).
  Proof.
    intros s1 s2 H.
    unfold CheriMemoryWithPNVI.get_allocation, CheriMemoryWithoutPNVI.get_allocation.
    subst.
    eapply bind_Same with (R':=mem_state_same).
    split.
    same_step.
    intros x1 x2 H.
    replace (ZMap.find (elt:=allocation) s2 (CheriMemoryWithoutPNVI.allocations x2))
      with (ZMap.find (elt:=allocation) s2 (CheriMemoryWithPNVI.allocations x1)).
    2: {
      apply find_m_Proper.
      reflexivity.
      apply H.
    }
    break_match.
    same_step.
    reflexivity.
    apply fail_noloc_same.
    reflexivity.
  Qed.

  Instance kill_same
    (loc : location_ocaml)
    (is_dyn : bool)
    (ptr1 ptr2 : pointer_value_indt)
    :
    pointer_value_eq ptr1 ptr2 ->
    Same eq
      (CheriMemoryWithPNVI.kill loc is_dyn ptr1)
      (CheriMemoryWithoutPNVI.kill loc is_dyn ptr1).
  Proof.
(*
    intros PE.
    invc PE.
    destruct b2;[cbn;destruct pr1; apply fail_same;split;split;reflexivity|].
    Opaque bind ret raise. (* TODO: move *)
    cbn.
    unfold CheriMemoryWithPNVI.kill, CheriMemoryWithPNVI.DEFAULT_FUEL.
    unfold CheriMemoryWithoutPNVI.kill, CheriMemoryWithoutPNVI.DEFAULT_FUEL.
    destruct pr1 eqn:P.
    - (* Prov_disabled *)
      unfold CheriMemoryWithPNVI.cap_is_null, CheriMemoryWithoutPNVI.cap_is_null.
      unfold CheriMemoryWithPNVI.cap_to_Z, CheriMemoryWithoutPNVI.cap_to_Z.
      repeat normalize_switches.
      break_match;[apply fail_same; auto|].
      same_step; split.
      apply find_live_allocation_same.
      intros.
      subst.
      destruct x2 eqn:X2.
      +
        break_let.
        break_match; break_match;[|apply fail_same; auto|same_step; auto|].
        *
          same_step;split.
          repeat break_match.
          1:apply fail_same; auto.
          1-9:try erewrite cap_match_dyn_allocation_same in * by eauto; try congruence.
          1-5: repeat normalize_switches;try lia.
          --
            (* tricky one! *)
            admit.
          --
            same_step;auto.
          --
            intros x1 x0 H.
            subst.
            same_step.
            intros m1 m2 H0.
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            split.
            cbn.
            break_match.
            unfold zmap_update_element.
            apply add_m_Proper;try reflexivity.
            apply remove_m_Proper;[reflexivity| apply H0].
            apply remove_m_Proper;[reflexivity| apply H0].
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            split;[cbn; apply H0|].
            apply H0.
        *
        *)
          (*
        break_match.
        same_step; reflexivity.
        same_step; reflexivity.
    - (* Prov_none *)
      repeat break_match; same_step; reflexivity.
    -
      break_match.
      repeat break_match; same_step; reflexivity.
      normalize_switches.
      unfold CheriMemoryWithPNVI.cap_is_null, CheriMemoryWithoutPNVI.cap_is_null.
      unfold CheriMemoryWithPNVI.cap_to_Z, CheriMemoryWithoutPNVI.cap_to_Z.
      break_match.
      repeat break_match; same_step; reflexivity.
      same_step.
      split.
      apply get_allocation_same;try reflexivity.
      intros x1 x2 H.
      subst.
      break_match.
      repeat break_match; same_step; reflexivity.
      admit.
    -
      admit.
    - (* Prov_device *)
      repeat break_match; same_step; reflexivity.
 *)
  Admitted.

 *)
 *)
End RevocationProofs.
