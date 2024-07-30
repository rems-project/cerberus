Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.ZArith.ZArith_dec.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Decidable.
From Coq.Strings Require Import String Ascii HexString.
From Coq.micromega Require Import Psatz Zify Lia.
Require Import Nsatz.

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

From Common Require Import SimpleError Utils ZMap AMap FMapExt.
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

(* Abstract tag definitions *)
Parameter abst_tagDefs: unit -> (SymMap.t CoqCtype.tag_definition).

Require Import ListSet.

Module ZMapProofs:= FMapExtProofs(Z_as_ExtOT)(ZMap).
Module AMapProofs:= FMapExtProofs(AddressValue_as_ExtOT)(AMap).

Module AbstTagDefs: TagDefs.
  Definition tagDefs := abst_tagDefs.
End AbstTagDefs.

(* This is a Morello-specific requirement. *)
Axiom pointer_sizeof_alignof: sizeof_pointer MorelloImpl.get = alignof_pointer MorelloImpl.get.

(* TODO: move *)
Section AddressValue_Lemmas.

  (* Algines given value up.
   *)
  Definition align_up addr alignment: Z
    :=
    let align := addr mod alignment in
    if align =? 0
    then addr (* already aligned *)
    else addr+(alignment - align).

  Lemma align_up_correct:
    forall ps addr : Z, 0 < ps -> (align_up addr ps) mod ps = 0.
  Proof.
    intros a b B.
    unfold align_up.
    break_match_goal; bool_to_prop_hyp.
    -
      assumption.
    -
      rewrite Z.add_sub_assoc.
      rewrite Zdiv.Zminus_mod.
      rewrite Zdiv.Zmod_mod.
      rewrite mod_add_r by lia.
      rewrite Z.sub_diag.
      apply Zdiv.Zmod_0_l.
  Qed.

  (** Predicate to check if address is pointer-aligned *)
  Definition addr_ptr_aligned (a:AddressValue.t) :=
    Z.modulo (AddressValue.to_Z a) (Z.of_nat (alignof_pointer MorelloImpl.get)) = 0.

  (** [a1] - [a2] for addresses *)
  Definition addr_offset (a1 a2:AddressValue.t) : Z
    := (AddressValue.to_Z a1) - (AddressValue.to_Z a2).

  (* TODO: move *)
  Lemma AdddressValue_eqb_eq:
    forall (a b: AddressValue.t),
      eqb a b = true <-> a = b.
  Proof.
    intros a b.
    split.
    -
      intros H.
      unfold eqb in H.
      bool_to_prop_hyp.
      apply bitvector.bv_eq.
      assumption.
    -
      intros H.
      unfold eqb.
      subst.
      lia.
  Qed.

  Lemma AdddressValue_eqb_neq:
    forall (a b: AddressValue.t),
      eqb a b = false <-> a <> b.
  Proof.
    intros a b.
    split.
    -
      intros H.
      unfold eqb in H.
      bool_to_prop_hyp.
      apply bitvector.bv_neq.
      assumption.
    -
      intros H.
      unfold eqb.
      apply bitvector.bv_neq in H.
      lia.
  Qed.

  Lemma AddressValue_ltb_Z_ltb:
    forall a b,
      AddressValue.ltb a b = Z.ltb (AddressValue.to_Z a) (AddressValue.to_Z b).
  Proof.
    reflexivity.
  Qed.

  Lemma AddressValue_eq_via_to_Z:
    forall a b,
      AddressValue.to_Z a = AddressValue.to_Z b <-> (a=b).
  Proof.
    split ; intros H.
    -
      unfold AddressValue.to_Z, bv_to_Z_unsigned in H.
      apply bitvector.bv_unsigned_inj.
      assumption.
    -
      subst.
      reflexivity.
  Qed.

  Lemma AddressValue_neq_via_to_Z:
    forall a b,
      AddressValue.to_Z a <> AddressValue.to_Z b <-> (a<>b).
  Proof.
    split ; intros; apply bitvector.bv_neq; assumption.
  Qed.

  Lemma AddressValue_of_Z_to_Z:
    forall a,
      AddressValue.of_Z (AddressValue.to_Z a) = a.
  Proof.
    intros a.
    unfold AddressValue.of_Z, AddressValue.to_Z.
    unfold bv_to_Z_unsigned.
    apply bitvector.Z_to_bv_bv_unsigned.
  Qed.

  Lemma with_offset_0:
    forall a,
      AddressValue.with_offset a (Z.of_nat 0) = a.
  Proof.
    intros a.
    unfold AddressValue.with_offset.
    replace (Z.of_nat O) with 0 by lia.
    rewrite Z.add_0_r.
    apply AddressValue_of_Z_to_Z.
  Qed.

  Lemma with_pos_offset_assoc:
    forall v a b,
      (0 <= a) ->
      (0 <= b) ->
      (0 <= (AddressValue.to_Z v) + (a + b) < AddressValue.ADDR_LIMIT) ->
      AddressValue.with_offset (AddressValue.with_offset v a) b = AddressValue.with_offset v (a + b).
  Proof.
    intros v a b A B [H1 H2].

    pose proof (AddressValue.to_Z_in_bounds v) as [V1 V2].
    apply AddressValue_eq_via_to_Z.
    rewrite 3!AddressValue.with_offset_no_wrap.
    lia.
    all: unfold AddressValue.ADDR_MIN in *; try lia.
    split.
    -
      rewrite AddressValue.with_offset_no_wrap;[lia|].
      unfold AddressValue.ADDR_MIN.
      lia.
    -
      rewrite AddressValue.with_offset_no_wrap;[lia|].
      unfold AddressValue.ADDR_MIN.
      lia.
  Qed.

  Lemma addr_offset_with_offset
    (a:AddressValue.t)
    (x:Z)
    (H: AddressValue.ADDR_MIN <= AddressValue.to_Z a + x < AddressValue.ADDR_LIMIT):

    addr_offset (AddressValue.with_offset a x) a = x.
  Proof.
    unfold addr_offset.
    rewrite AddressValue.with_offset_no_wrap.
    lia.
    apply H.
  Qed.

  Lemma with_offset_addr_offset:
    forall a1 a2,
      (AddressValue.with_offset a1 (addr_offset a2 a1)) = a2.
  Proof.
    intros a1 a2.
    unfold addr_offset.
    unfold AddressValue.with_offset.
    replace (AddressValue.to_Z a1 + (AddressValue.to_Z a2 - AddressValue.to_Z a1))
      with (AddressValue.to_Z a2) by lia.
    rewrite AddressValue_of_Z_to_Z.
    reflexivity.
  Qed.

  Lemma addr_offset_bounds:
    forall a b,
      (AddressValue.ADDR_MIN - AddressValue.ADDR_LIMIT + 1) <= (addr_offset a b) <= (AddressValue.ADDR_LIMIT - AddressValue.ADDR_MIN - 1).
  Proof.
    intros a b.
    pose proof (AddressValue.to_Z_in_bounds a).
    pose proof (AddressValue.to_Z_in_bounds b).
    unfold addr_offset.
    lia.
  Qed.

End AddressValue_Lemmas.

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


(* Should be in ProofAux.v but it depends on stdpp. *)
Lemma lookup_elements_MapsTo
  {A: Type}
  (m : AMap.M.t A)
  (k: AMap.M.key)
  (v : A):
  (exists k', base.lookup k' (AMap.M.elements (elt:=A) m) = Some (k, v)) -> AMap.M.MapsTo k v m.
Proof.
  intros [k' ES].
  apply AMap.M.elements_2.
  apply list.elem_of_list_lookup_2 in ES.
  apply base.elem_of_list_In in ES.
  apply InA_alt.
  exists (k,v).
  split.
  -
    unfold AMap.M.eq_key_elt, AMap.M.Raw.Proofs.PX.eqke.
    split; reflexivity.
  -
    assumption.
Qed.

Module Type CHERISwitches <: CerbSwitchesDefs.
  Include CerbSwitchesDefs.
  Parameter get_switches_val:
    get_switches tt = [SW_revocation INSTANT; SW_strict_pointer_equality; SW_pointer_arith STRICT;
                       SW_strict_pointer_relationals; SW_strict_reads; SW_CHERI].
End CHERISwitches.

Module CHERISwitchesExe : CHERISwitches.
  Definition get_switches (_:unit)
    := [SW_revocation INSTANT; SW_strict_pointer_equality; SW_pointer_arith STRICT;
        SW_strict_pointer_relationals; SW_strict_reads; SW_CHERI].

  Lemma get_switches_val:
    get_switches tt = [SW_revocation INSTANT; SW_strict_pointer_equality; SW_pointer_arith STRICT;
                       SW_strict_pointer_relationals; SW_strict_reads; SW_CHERI].
  Proof.
    reflexivity.
  Qed.

End CHERISwitchesExe.

Module CheriMemoryImplWithProofs
<:
  CheriMemoryImpl(MemCommonExe)(Capability_GS)(MorelloImpl)(AbstTagDefs)(CHERISwitchesExe).
  Include CheriMemoryExe(MemCommonExe)(Capability_GS)(MorelloImpl)(AbstTagDefs)(CHERISwitchesExe).

  (* --- Equality predicates for types used in Memory Models --- *)

  (* Check whether this cap base address within allocation *)
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
     using. In particular, instant revocation is assumed *)
  Inductive single_alloc_id_cap_cmp (allocs: ZMap.M.t allocation) (alloc_id: Z) c1 c2 : Prop
    :=
  | single_cap_cmp_live:
    (* The allocation ID is mapped to an allocation *)
    forall a, ZMap.M.MapsTo alloc_id a allocs ->
         cap_match_with_alloc a c1 c2 -> (* then match c1 to c2 based on alloc_id *)
         single_alloc_id_cap_cmp allocs alloc_id c1 c2
  | single_cap_cmp_dead:
    (* The allocation ID is not mapped to an allocation *)
    ~ ZMap.M.In alloc_id allocs ->
    Capability_GS.cap_invalidate c1 = c2 ->
    single_alloc_id_cap_cmp allocs alloc_id c1 c2.


  Definition decode_cap (bs:list (option ascii)) (tag:bool) (c:Capability_GS.t): Prop
    :=
    exists ls:list ascii,
      (* have their corrsponding bytes intialized *)
      Forall2 (fun a x => a = Some x) bs ls
      (* decode without error *)
      /\ Capability_GS.decode ls true = Some c.

  Definition allocations_do_no_overlap (a1 a2:allocation) : Prop
    :=
    let a1_base := AddressValue.to_Z a1.(base) in
    let a2_base := AddressValue.to_Z a2.(base) in
    let a1_size := Z.of_nat a1.(size) in
    let a2_size := Z.of_nat a2.(size) in
    (a1_base + a1_size <= a2_base) \/ (a2_base + a2_size <= a1_base) \/ a1_size = 0 \/ a2_size = 0.

  Definition base_mem_invariant (m: mem_state_r) : Prop
    :=
    let cm := m.(capmeta) in
    let am := m.(allocations) in

    (* All allocations are live. [allocation.(is_dead)] is only used
      for Conucopia. For others, the dead allocations are immediately
      removed.  *)
    ZMapProofs.map_forall (fun a => a.(is_dead) = false) am

    (* live allocatoins do not overlap *)
    /\ (forall alloc_id1 alloc_id2 a1 a2,
          alloc_id1 <> alloc_id2 ->
          ZMap.M.MapsTo alloc_id1 a1 am ->
          ZMap.M.MapsTo alloc_id2 a2 am ->
          allocations_do_no_overlap a1 a2)
    (* all allocations have upper bound *)
    /\
      ZMapProofs.map_forall (fun a => AddressValue.to_Z a.(base) + (Z.of_nat a.(size)) <= AddressValue.ADDR_LIMIT) am

    (* All keys in capmeta must be pointer-aligned addresses *)
    /\ AMapProofs.map_forall_keys addr_ptr_aligned cm

    (* [next_alloc_id] is sane *)
    /\
      ZMapProofs.map_forall_keys (fun alloc_id => alloc_id < m.(next_alloc_id)) am
    (* [last_address] is sane *)
    /\
      ZMapProofs.map_forall (fun a => AddressValue.to_Z a.(base) >= AddressValue.to_Z m.(last_address)) am.

  Ltac destruct_base_mem_invariant H
    :=
    let Bdead := fresh "Bdead" in
    let Bnooverlap := fresh "Bnooverlap" in
    let Bfit := fresh "Bfit" in
    let Balign := fresh "Balign" in
    let Bnextallocid := fresh "Bnextallocid" in
    let Blastaddr := fresh "Blastaddr" in
    destruct H as [Bdead [Bnooverlap [Bfit [Balign [Bnextallocid Blastaddr]]]]].

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
    (capmeta: AMap.M.t (bool*CapGhostState)):
    (AddressValue.to_Z addr) + (Z.of_nat size) <= AddressValue.ADDR_LIMIT ->
    forall a tg,
      AMap.M.MapsTo a tg (init_ghost_tags addr size capmeta)
      ->
        ( (* existing *)
          AMap.M.MapsTo a tg capmeta
          \/
            ( (* new *)
              addr_ptr_aligned a
              /\
                tg = (false, {| tag_unspecified := true; bounds_unspecified := false |})
            )
        ).
  Proof.
    intros L a tg H.
    unfold addr_ptr_aligned.
    unfold init_ghost_tags, align_down in *.
    break_match_hyp;[left;assumption|].
    clear size Heqn.
    rename n into size'. (* size - 1 *)
    apply amap_range_init_spec in H.
    destruct H as [[H1 H2] | [[i [H3 H4]] H5]].
    -
      (* Not in range *)
      left.
      apply H2.
    -
      (* in range *)
      right.
      split;[|assumption].

      (* prep work *)
      clear H5 tg capmeta.
      pose proof (AddressValue.to_Z_in_bounds addr) as H.
      destruct H as [LA HA].
      remember (Z.of_nat (alignof_pointer MorelloImpl.get)) as ps.
      assert(0<ps).
      {
        pose proof MorelloImpl.alignof_pointer_pos.
        subst ps.
        lia.
      }
      clear Heqps.
      rename addr into addr'.
      remember (AddressValue.to_Z addr') as addr.
      clear addr' Heqaddr.
      (* end prep *)


      (* used twice below *)
      assert(AddressValue.ADDR_MIN <= addr - addr mod ps < AddressValue.ADDR_LIMIT) as A.
      {
        unfold AddressValue.ADDR_MIN,
          AddressValue.ADDR_LIMIT,
          AddressValue.len,
          bitvector.bv_modulus
          in *.
        split.
        --
          pose proof (Z.mod_le addr ps LA H).
          lia.
        --
          pose proof (Z.mod_le addr ps LA H).
          cut(addr - addr mod ps <= addr).
          lia.
          cut (0 <= addr mod ps).
          lia.
          apply numbers.Z.mod_pos.
          assumption.
      }

      subst a.
      setoid_rewrite Z.mul_comm.
      rewrite AddressValue.with_offset_no_wrap.
      +
        rewrite AddressValue.of_Z_roundtrip by auto.
        rewrite Z.mul_comm, Zdiv.Z_mod_plus_full.
        unfold AddressValue.ADDR_MIN in *.
        apply align_bottom_correct;assumption.
      +
        rewrite AddressValue.of_Z_roundtrip by auto.
        unfold AddressValue.ADDR_MIN,
          AddressValue.ADDR_LIMIT,
          AddressValue.len,
          bitvector.bv_modulus
          in *.
        split.
        --
          pose proof (Z.mod_le addr ps LA H).
          lia.
        --
          replace (Z.of_N 64) with 64 in * by lia.

          remember (Z.to_nat ((addr + Z.of_nat size' - (addr + Z.of_nat size') mod ps - (addr - addr mod ps)) / ps)) as n.
          assert(i<=n)%nat by lia; clear H3.

          cut(addr - addr mod ps + ps * Z.of_nat n < 2 ^ 64).
          {
            intros H1.
            clear Heqn.
            revert i H0.
            induction n; intros.
            -
              lia.
            -
              destruct (Nat.eq_dec i (S n)).
              lia.
              apply IHn;try lia.
          }
          zify.
          destruct H2;
            clear __sat3 __sat4;
            destruct H1; [|lia].
          ++
            rewrite <- H2 in H1.


            rename size' into tmp;
              remember (Z.of_nat tmp) as size';
              clear tmp Heqsize'.
            rename z2 into zn.

            rename i into i';
              remember (Z.of_nat i') as i;
              clear i' Heqi.

            destruct A as [A0 A].

            rewrite Z.add_assoc in L.
            remember (addr + size') as lastaddr.
            remember (addr - addr mod ps) as a0.
            remember (lastaddr - lastaddr mod ps) as a1.

            assert(i <= zn) by lia ; clear H3.

            subst zn.
            rewrite H2.
            rewrite <- Zdiv.Z_div_exact_2.
            2: lia.
            2: {
              subst a1 a0.

              apply sub_mod_0.
              apply align_bottom_correct.
              assumption.
              apply align_bottom_correct.
              assumption.
            }
            replace (a0 + (a1 - a0)) with a1 by lia.
            subst a1.
            assert(0<=lastaddr mod ps).
            {
              apply numbers.Z.mod_pos.
              lia.
            }
            lia.
  Qed.

  (* It shows show:
     1. No new keys introduced to [capmeta]
     2. Tag change monotonicity
   *)
  Lemma capmeta_ghost_tags_monotone
    (addr: AddressValue.t)
    (size: nat)
    (capmeta: AMap.M.t (bool*CapGhostState)):
    forall a tg' gs',
      AMap.M.MapsTo a (tg',gs') (capmeta_ghost_tags addr size capmeta)
      ->
        exists tg gs,
          AMap.M.MapsTo a (tg,gs) capmeta /\
            (
              (* unchanged. outside of range, was false or was unspecified *)
              (tg = tg' /\ gs = gs')
              \/
                (* ghosted. only when in range and was true and specified *)
                (tg = true /\ gs.(tag_unspecified) = false /\
                   tg' = true /\ gs'.(tag_unspecified) = true)
            ).
  Proof.
    intros a tg' gs' H.
    destruct size.
    -
      exists tg', gs'.
      split;auto.
    -
      cbn in *.
      apply AMap.F.mapi_inv in H.
      destruct H as [(tg,gs) [a' [E H]]].
      subst a'.
      break_match_hyp.
      +
        destruct H.
        tuple_inversion.
        bool_to_prop_hyp.
        subst.
        exists true, gs.
        split;auto.
        right.
        split;auto.
        split.
        apply negb_true_iff in H.
        apply H.
        split;tauto.
      +
        destruct H.
        tuple_inversion.
        bool_to_prop_hyp;(exists tg,gs;split;auto).
  Qed.


  (* Another spec for [capmeta_ghost_tags]. Affected range expressed in aligned addresses *)
  Fact capmeta_ghost_tags_spec_in_range_aligned
    (addr: AddressValue.t)
    (size: nat)
    (SZ: (size>0)%nat)
    (capmeta: AMap.M.t (bool*CapGhostState)):

    forall a,
      let alignment := Z.of_nat (alignof_pointer MorelloImpl.get) in
      let a0 := align_down (AddressValue.to_Z addr) alignment in
      let a1 := align_down (AddressValue.to_Z addr + ((Z.of_nat size) - 1)) alignment in
      (a0 <= AddressValue.to_Z a <= a1) ->
      forall tg gs,
        AMap.M.MapsTo a (tg,gs) (capmeta_ghost_tags addr size capmeta)
        ->
          tg=false \/ gs.(tag_unspecified) = true.
  Proof.
    intros a alignment a0 a1 R tg gs M.
    subst a0 a1 alignment.
    dependent destruction size.
    -
      lia.
    -
      cbn in *.
      apply AMap.F.mapi_inv in M.
      destruct M as [(tg',gs') [a' [E M]]].
      subst a'.
      break_match_hyp.
      +
        (* in range *)
        destruct M.
        tuple_inversion.
        bool_to_prop_hyp.
        subst.
        rename gs' into gs.
        right.
        split;auto.
      +
        rename size0 into size.
        destruct M.
        tuple_inversion.
        rename tg' into tg, gs' into gs.
        bool_to_prop_hyp.
        * (* unspecified *)
          apply negb_false_iff in H.
          auto.
        *
          (* untagged *)
          auto.
        *
          (* az < a0 *)
          exfalso.
          unfold align_down in *.
          pose proof MorelloImpl.alignof_pointer_pos as P.
          zify.
          subst.
          lia.
        *
          (* a1 < az *)
          exfalso.
          unfold align_down in *.
          pose proof MorelloImpl.alignof_pointer_pos as P.
          zify.
          subst.
          rewrite Z.add_simpl_r in  *.
          lia.
  Qed.

  Fact mod_le_mod
    (a b c: Z)
    (Cpos: 0 < c)
    (Anneg: 0 <= a)
    (Bnneg: 0 <= b)
    (Hab: a <= b):
    a - a mod c <= b - b mod c.
  Proof.
    remember (a mod c) as r_a.
    remember (b mod c) as r_b.
    remember (a / c) as q_a.
    remember (b / c) as q_b.

    assert (H_a: a = q_a * c + r_a).
    {
      subst.
      rewrite Z.mul_comm.
      apply Z.div_mod.
      lia.
    }
    assert (H_b: b = q_b * c + r_b).
    {
      subst.
      rewrite Z.mul_comm.
      apply Z.div_mod.
      lia.
    }

    destruct (Z.eq_dec q_a q_b).
    +
      subst.
      lia.
    +
      pose proof (Z.mod_pos_bound a c Cpos).
      pose proof (Z.mod_pos_bound b c Cpos).
      subst a b.
      nia.
  Qed.


  Fact mod_le_mod_inv
    (a b c: Z)
    (Cpos: 0 < c)
    (Anneg: 0 <= a)
    (Bnneg: 0 <= b):
    (a - a mod c < b - b mod c) ->
    a < b.
  Proof.
    intros H.

    pose proof (Z.mod_pos_bound a c Cpos) as Ba.
    pose proof (Z.mod_pos_bound b c Cpos) as Bb.

    remember (a mod c) as r_a.
    remember (b mod c) as r_b.
    remember (a / c) as q_a.
    remember (b / c) as q_b.

    assert (H_a: a = q_a * c + r_a).
    {
      subst.
      rewrite Z.mul_comm.
      apply Z.div_mod.
      lia.
    }
    assert (H_b: b = q_b * c + r_b).
    {
      subst.
      rewrite Z.mul_comm.
      apply Z.div_mod.
      lia.
    }
    destruct (Z.eq_dec q_a q_b) as [E|NE].
    +
      subst q_b.
      rename q_a into q.
      nia.
    +
      nia.
  Qed.


  (* Yet another spec for [capmeta_ghost_tags].  It is defined for
     unalinged address range and more suitable to be applied when
     unaligned region is ghosted.  *)
  Lemma capmeta_ghost_tags_spec_in_range
    (addr: AddressValue.t)
    (size: nat)
    (capmeta: AMap.M.t (bool*CapGhostState))
    (SZ: (size>0)%nat)
    :

    forall a,
      (0 <= addr_offset a addr < Z.of_nat size) ->

      let alignment := Z.of_nat (alignof_pointer MorelloImpl.get) in
      let ac := AddressValue.of_Z (align_down (AddressValue.to_Z a) alignment) in
      forall tg gs,
        AMap.M.MapsTo ac (tg,gs) (capmeta_ghost_tags addr size capmeta)
        ->
          tg=false \/ gs.(tag_unspecified) = true.
  Proof.
    intros a H alignment ac tg gs H0.
    apply (capmeta_ghost_tags_spec_in_range_aligned addr size SZ capmeta ac);
      subst ac alignment.
    2: auto.

    (* cleanup *)
    clear H0 capmeta tg gs.
    destruct H.
    unfold align_down, addr_offset in *.

    (* generalize alignment *)
    pose proof MorelloImpl.alignof_pointer_pos as P.
    remember (Z.of_nat (alignof_pointer MorelloImpl.get)) as zalign.
    assert (0<zalign) as ZP by lia.
    clear Heqzalign P.
    rename zalign into align.

    (* generalize size *)
    remember (Z.of_nat size) as zsz.
    assert (zsz > 0) as ZSZ by lia.
    clear size SZ Heqzsz.
    rename zsz into sz.

    (* some random useful facts *)
    pose proof (AddressValue.to_Z_in_bounds addr).
    pose proof (AddressValue.to_Z_in_bounds a).
    unfold AddressValue.ADDR_MIN in *.
    pose proof (Z.mod_pos_bound (AddressValue.to_Z addr) align ZP).
    pose proof (Z.mod_pos_bound (AddressValue.to_Z a) align ZP).

    (* need the following two for roundtrip simplification *)
    pose proof (Z.mod_bound_pos_le (AddressValue.to_Z addr) align).
    autospecialize H5;[lia|].
    autospecialize H5;[lia|].
    pose proof (Z.mod_bound_pos_le (AddressValue.to_Z a) align).
    autospecialize H6;[lia|].
    autospecialize H6;[lia|].

    (* simplify *)
    rewrite AddressValue.of_Z_roundtrip;[|unfold AddressValue.ADDR_MIN;lia].

    split;apply mod_le_mod;lia.
  Qed.

  Fact capmeta_ghost_tags_spec_outside_range_aligned
    (addr: AddressValue.t)
    (size: nat)
    (SZ: (size>0)%nat)
    (capmeta: AMap.M.t (bool*CapGhostState)):

    forall a,
      let alignment := Z.of_nat (alignof_pointer MorelloImpl.get) in
      let a0 := align_down (AddressValue.to_Z addr) alignment in
      let a1 := align_down (AddressValue.to_Z addr + ((Z.of_nat size) - 1)) alignment in
      not (a0 <= AddressValue.to_Z a <= a1) ->
      forall tg gs,
        AMap.M.MapsTo a (tg,gs) (capmeta_ghost_tags addr size capmeta)
        ->
          AMap.M.MapsTo a (tg,gs) capmeta.
  Proof.
    intros a alignment a0 a1 R tg gs M.
    subst a0 a1 alignment.
    destruct size.
    -
      lia.
    -
      cbn in *.
      apply AMap.F.mapi_inv in M.
      destruct M as [(tg',gs') [a' [E M]]].
      subst a'.
      break_match_hyp.
      +
        (* changed *)
        contradict R.
        pose proof MorelloImpl.alignof_pointer_pos as P.
        zify.
        subst.
        split;try lia.
        replace (Z.of_nat (S size0) - 1) with (Z.of_nat size0) by lia.
        lia.
      +
        (* unchanged *)
        destruct M.
        tuple_inversion.
        assumption.
  Qed.

  (* Yet another spec for [capmeta_ghost_tags]. It is defined for
     address range whose capabilites are affected.  *)
  Lemma capmeta_ghost_tags_spec_in_extended
    (addr: AddressValue.t)
    (size: nat)
    (SZ: (size>0)%nat)
    (capmeta: AMap.M.t (bool*CapGhostState)):

    forall a,
      let alignment := Z.of_nat (alignof_pointer MorelloImpl.get) in
      let a0 := align_down (AddressValue.to_Z addr) alignment in
      let a1 := align_up (AddressValue.to_Z addr + ((Z.of_nat size) - 1)) alignment in
      (a0 <= AddressValue.to_Z a <= a1) ->
      forall tg gs,
        AMap.M.MapsTo a (tg,gs) (capmeta_ghost_tags addr size capmeta)
        ->
          tg=false \/ gs.(tag_unspecified) = true.
  Proof.
    intros a alignment a0 a1 R tg gs M.
    assert(AddressValue.to_Z a mod alignment = 0) as AA. admit. (* from MapsTo *)
    subst a0 a1 alignment.
    dependent destruction size.
    -
      lia.
    -
      cbn in *.
      apply AMap.F.mapi_inv in M.
      destruct M as [(tg',gs') [a' [E M]]].
      subst a'.
      break_match_hyp.
      +
        (* in range *)
        destruct M.
        tuple_inversion.
        bool_to_prop_hyp.
        subst.
        rename gs' into gs.
        right.
        split;auto.
      +
        (* outside range *)
        rename size0 into size.
        destruct M.
        tuple_inversion.
        rename tg' into tg, gs' into gs.
        bool_to_prop_hyp.
        * (* unspecified *)
          apply negb_false_iff in H.
          auto.
        *
          (* untagged *)
          auto.
        *
          (* az < a0 *)
          exfalso.
          unfold align_down in *.
          pose proof MorelloImpl.alignof_pointer_pos as P.
          zify.
          subst.
          lia.
        *
          (* a1 < az *)
          exfalso.
          clear H0 tg gs capmeta0 SZ.

          destruct R2 as [R1 R2].

          (* genralization *)
          remember (Z.of_nat (alignof_pointer MorelloImpl.get)) as alignment.
          assert(0 < alignment).
          {
            pose proof MorelloImpl.alignof_pointer_pos.
            lia.
          }
          clear Heqalignment.


          unfold align_down in *.
          zify.
          subst.

          pose proof (align_up_correct alignment (AddressValue.to_Z addr + (Z.of_nat (S size) - 1)) ) as AC1.
          unfold align_up in *.
          break_if;bool_to_prop_hyp.
          --
            clear R1 AA.
            replace (Z.of_nat (S size) - 1) with (Z.of_nat size) in * by lia.
            rewrite Heqb in H.
            lia.
          --
            specialize (AC1 H0).
            replace (Z.of_nat (S size) - 1) with (Z.of_nat size) in * by lia.

            pose proof (AddressValue.to_Z_in_bounds addr).
            pose proof (AddressValue.to_Z_in_bounds a).
            unfold AddressValue.ADDR_MIN in *.

            (* generalization *)
            remember (AddressValue.to_Z a) as az.
            clear Heqaz a.
            rename az into a.

            (* generalization *)
            remember (AddressValue.to_Z addr) as addrz.
            clear Heqaddrz addr.
            rename addrz into addr.

            (* size to Z *)
            remember (Z.of_nat size) as sz.
            assert (0<=sz) by lia.
            clear Heqsz size.

            remember (addr + sz) as a1.

            pose proof (Z.mod_pos_bound a1 alignment H0).
            pose proof (Z.mod_pos_bound a alignment H0).

            pose proof (Z.mod_bound_pos_le a1 alignment).
            autospecialize H6;[lia|].
            autospecialize H6;[lia|].
            pose proof (Z.mod_bound_pos_le a alignment).
            autospecialize H7;[lia|].
            autospecialize H7;[lia|].

            remember (a1 mod alignment) as r_a1.

            (* R2 vs H *)
            clear cstr.
            assert(0 <= a1) by lia.
            clear Heqa1 addr R1 sz H1 H3.

  Admitted. (* TODO: postponed. Only needed by [memcpy_copy_data_PreservesInvariant] *)

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
  Qed.
  Opaque ret bind.

  Instance zmap_sequence_SameState
    {A: Type}
    (mv: ZMap.M.t (memM A)):
    ZMapProofs.map_forall SameState mv ->
    SameState (ZMap.map_sequence mv).
  Proof.
    intros H.
    unfold ZMap.map_sequence.
    break_let.
    pose proof (sequence_same_state l0) as SS.
    autospecialize SS.
    eapply ZMapProofs.map_forall_Forall_elements;eauto.
    clear H.
    apply bind_SameState.
    assumption.
    intros x.
    apply ret_SameState.
  Qed.

  Instance amap_sequence_SameState
    {A: Type}
    (mv: AMap.M.t (memM A)):
    AMapProofs.map_forall SameState mv ->
    SameState (AMap.map_sequence mv).
  Proof.
    intros H.
    unfold AMap.map_sequence.
    break_let.
    pose proof (sequence_same_state l0) as SS.
    autospecialize SS.
    eapply AMapProofs.map_forall_Forall_elements;eauto.
    clear H.
    apply bind_SameState.
    assumption.
    intros x.
    apply ret_SameState.
  Qed.


  Instance zmap_mmapi_SameState
    {A B: Type}
    (c: ZMap.M.key -> A -> memM B)
    (zm : ZMap.M.t A):

    (forall k v, SameState (c k v)) ->
    SameState (ZMap.map_mmapi c zm).
  Proof.
    intros C zm' m0 m1 H.
    unfold ZMap.map_mmapi in H.
    apply zmap_sequence_SameState in H;[assumption|].
    clear H.

    unfold ZMapProofs.map_forall.
    intros k v H.
    apply ZMap.F.mapi_inv in H.
    destruct H as [a [k' [H1 [H2 H3]]]].
    subst.
    apply C.
  Qed.

  Instance amap_mmapi_SameState
    {A B: Type}
    (c: AMap.M.key -> A -> memM B)
    (zm : AMap.M.t A):

    (forall k v, SameState (c k v)) ->
    SameState (AMap.map_mmapi c zm).
  Proof.
    intros C zm' m0 m1 H.
    unfold AMap.map_mmapi in H.
    apply amap_sequence_SameState in H;[assumption|].
    clear H.

    unfold AMapProofs.map_forall.
    intros k v H.
    apply AMap.F.mapi_inv in H.
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
  Qed.
  Opaque ret bind liftM.

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
  Qed.
  Opaque ret bind get.

  Instance get_allocation_opt_SameState
    (alloc_id : Z):
    SameState (get_allocation_opt alloc_id).
  Proof.
    intros res s s' H.
    Transparent ret bind get.
    unfold get_allocation_opt, bind, get, ret, memM_monad, Monad_errS, State_errS in H.
    tuple_inversion.
    reflexivity.
  Qed.
  Opaque ret bind get.

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
    ZMap.M.MapsTo alloc_id alloc s'.(allocations).
  Proof.
    intros H.
    unfold find_live_allocation in H.
    Transparent ret bind get.
    unfold bind, get, ret, memM_monad, Monad_errS, State_errS in H.
    Opaque ret bind get.
    tuple_inversion.
    revert H2.
    match goal with
    | [ |- context[ZMap.M.fold ?f _ _]] =>
        remember f as ff
    end.
    revert alloc_id alloc.
    cut(
        (fun res =>
           match res with
           | None => True
           | Some (alloc_id, alloc) => ZMap.M.MapsTo alloc_id alloc (allocations s')
           end) (ZMap.M.fold ff (allocations s') None)).
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
    apply ZMap.P.fold_rec_nodep.
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
    (addr : AMap.M.key)
    (bm : AMap.M.t (option ascii))
    (sz: nat):
    Datatypes.length (fetch_bytes bm addr sz) = sz.
  Proof.
    unfold fetch_bytes.
    rewrite map_length.
    rewrite list_init_len.
    reflexivity.
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
    (addr: AMap.M.key)
    (c: Capability_GS.t)
    (bm: AMap.M.t (option ascii)):
    decode_cap (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)) true c ->
    fetch_and_decode_cap bm addr true = inr c.
  Proof.
      intros D.
      remember (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)) as bs.
      unfold decode_cap in D.
      unfold fetch_and_decode_cap.
      Transparent ret bind get.
      unfold memM_monad, Monad_errS, State_errS, Monad_either, ret, bind.
      generalize dependent (fetch_bytes bm addr (sizeof_pointer MorelloImpl.get)).
      intros bs' E.
      subst bs'.
      break_match.
      -
        exfalso.
        unfold option2serr in Heqs.
        break_match_hyp.
        inv Heqs.
        destruct D as [ls [BL D]].
        rename Heqs into BC.
        apply extract_unspec_spec in BL.
        congruence.
      -
        destruct D as [ls [BL D]].
        (* [bs] [cs] and [ls] relation is a bit tricky here, but workable *)

        apply extract_unspec_spec in BL.
        rewrite BL in Heqs.
        cbn in Heqs.
        invc Heqs.
        rewrite D.
        reflexivity.
  Qed.
  Opaque ret bind get.

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

  (* TODO: add to [inv_step] *)
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

  Lemma raise_either_inr_inv
    {A:Type}
    {e: string}
    {a : A}:
    @raise string serr (Exception_either string) A e =
      @inr string A a -> False.
  Proof.
    intros H.
    Transparent raise.
    unfold raise, Exception_either in H.
    inversion H.
  Qed.

  Lemma raise_serr_inr_inv
    {A:Type}
    {e: string}
    {a : A}:
    @raise string serr Exception_serr A e =
      @inr string A a -> False.
  Proof.
    intros H.
    Transparent raise.
    unfold raise, Exception_serr in H.
    inversion H.
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

  Lemma put_inv:
    forall s s' st u,
      @put mem_state_r memM (State_errS mem_state memMError)
        s st =
        (s', @inr memMError unit u) -> s = s'.
  Proof.
    intros s s' st u H.

    Transparent put.
    unfold put, State_errS in H.
    Opaque put.
    inversion H.
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
    {m: serr A}
    {s s': mem_state}:
    serr2InternalErr m s = (s', inr x) -> m = inr x.
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

  Lemma bind_sassert_inv
    {T: Type}
    (msg: string)
    (cond: bool)
    {c: unit -> serr T}
    {x: T}
    :
    (@bind (sum string) (Monad_either string) unit T (sassert cond msg) c) = inr x ->
    cond = true /\  c tt = inr x.
  Proof.
    Transparent bind ret.
    unfold bind, ret, memM_monad, Monad_errS, Monad_either.
    Opaque bind ret.
    unfold sassert.
    repeat break_match.
    -
      inv Heqs.
    -
      apply raise_serr_inl in Heqs.
      invc Heqs.
      intros H.
      inv H.
    -
      rewrite ret_serr_inv in Heqs.
      invc Heqs.
      intros H.
      split;auto.
    -
      apply raise_serr_inr_inv in Heqs.
      tauto.
  Qed.

  Ltac htrim :=
    repeat break_match_hyp; repeat break_let; try subst; try tuple_inversion; cbn in *; try discriminate.

  Ltac state_inv_step :=
    repeat match goal with
      (* bind sassert *)
      |[H: (@bind (sum string) (Monad_either string) unit _ (sassert _ _) _) = inr _ |- _] =>
          let H1 := fresh H in
          let H2 := fresh H in
          apply bind_sassert_inv in H;
          destruct H as [H1 H2]
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
      | [H: fail _ _ _ = (_, inr _) |- _] =>
          (* idtac H "fail"; *)
          apply fail_inr_inv in H; tauto
          ; htrim
      | [H: serr2InternalErr _ _ = (_, inr _) |- _] =>
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
      | [H: put _ _ = (_, inr _) |- _] =>
          (* idtac H "put"; *)
          apply put_inv in H
          ; htrim
      | [H: sassert _ _ = inr _ |- _] =>
          (* idtac H "sassert"; *)
          apply sassert_inv in H
          ; htrim
      | [H: inl _ = inl _ |- _] => inversion H; clear H; htrim
      | [H: inr _ = inr _ |- _] => inversion H; clear H; htrim
      | [H: @raise string _ Exception_serr unit _ = @inl string unit _ |- _] =>
          apply raise_serr_inl in H;
          inversion H;
          clear H;
          htrim
      | [H: @raise string serr Exception_serr unit _ = @inr string unit _ |- _] =>
          apply raise_serr_inr_inv in H; tauto
      | [H: @raise string serr (Exception_either string) _ _ = @inr string _ _ |- _] =>
          apply raise_either_inr_inv in H; tauto
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
        (invr s -> invr (f s)) ->
        PreservesInvariant s (ErrorWithState.update f).
    Proof.
      intros s H MI.
      specialize (H MI).
      unfold post_exec_invariant, lift_sum_p.
      break_match_goal.
      tauto.
      unfold execErrS, evalErrS, lift_sum_p in Heqs0.
      break_let.
      break_match_hyp.
      inv Heqs0.
      apply ret_inr in Heqs0.
      invc Heqs0.
      destruct u.
      Transparent ErrorWithState.update get put bind.
      unfold ErrorWithState.update, bind, get, put, Monad_errS, State_errS in Heqp.
      Opaque ErrorWithState.update get put bind.
      tuple_inversion.
      apply H.
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
      (mv: ZMap.M.t (memM A)):
      forall s,
        (forall k v, ZMap.M.MapsTo k v mv -> forall s', PreservesInvariant s' v) ->
        PreservesInvariant s (ZMap.map_sequence mv).
    Proof.
      intros s H.
      apply ZMapProofs.map_maps_to_elements_p in H.
      unfold ZMap.map_sequence.
      break_let.
      apply bind_PreservesInvariant.
      -
        apply sequence_PreservesInvariant.
        generalize dependent (ZMap.M.elements (elt:=memM A) mv).
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

    Instance amap_sequence_PreservesInvariant
      {A: Type}
      (mv: AMap.M.t (memM A)):
      forall s,
        (forall k v, AMap.M.MapsTo k v mv -> forall s', PreservesInvariant s' v) ->
        PreservesInvariant s (AMap.map_sequence mv).
    Proof.
      intros s H.
      apply AMapProofs.map_maps_to_elements_p in H.
      unfold AMap.map_sequence.
      break_let.
      apply bind_PreservesInvariant.
      -
        apply sequence_PreservesInvariant.
        generalize dependent (AMap.M.elements (elt:=memM A) mv).
        intros ls H S.
        clear mv.
        rename l into lk, l0 into lv.
        apply Forall_nth.
        intros k v L.
        rewrite Forall_nth in H.
        specialize (H k (nth k lk (AddressValue.of_Z 0), v)).

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
      (f : ZMap.M.key -> A -> memM B)
      (zm: ZMap.M.t A):
      forall s,
        (forall k x, forall s', PreservesInvariant s' (f k x)) ->
        PreservesInvariant s (@ZMap.map_mmapi A B memM memM_monad f zm).
    Proof.
      intros s H.
      unfold ZMap.map_mmapi.
      apply zmap_sequence_PreservesInvariant.
      intros k v H0.
      apply ZMap.F.mapi_inv in H0.
      destruct H0 as [v' [k' [E [E1 M]]]].
      subst.
      apply H.
    Qed.

    Instance amap_mmapi_PreservesInvariant
      {A B : Type}
      (f : AMap.M.key -> A -> memM B)
      (zm: AMap.M.t A):
      forall s,
        (forall k x, forall s', PreservesInvariant s' (f k x)) ->
        PreservesInvariant s (@AMap.map_mmapi A B memM memM_monad f zm).
    Proof.
      intros s H.
      unfold AMap.map_mmapi.
      apply amap_sequence_PreservesInvariant.
      intros k v H0.
      apply AMap.F.mapi_inv in H0.
      destruct H0 as [v' [k' [E [E1 M]]]].
      subst.
      apply H.
    Qed.

  End MemMwithInvariant.


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


  Lemma resolve_has_INSTANT:
    has_switch (CHERISwitchesExe.get_switches tt) (SW_revocation INSTANT) = true.
  Proof.
    unfold has_switch.
    rewrite CHERISwitchesExe.get_switches_val.
    apply set_mem_correct2.
    cbv.
    left;reflexivity.
  Qed.

  Lemma resolve_has_CORNUCOPIA:
    has_switch (CHERISwitchesExe.get_switches tt) (SW_revocation CORNUCOPIA) = false.
  Proof.
    rewrite CHERISwitchesExe.get_switches_val.
    unfold has_switch.
    apply set_mem_complete2.
    intros H.
    repeat (destruct H;[discriminate|]).
    inv H.
  Qed.

  (* memory invariant

     It will work only for instant revocation. In the case of
     Cornucopia the invariant will be different.  *)
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
          AMap.M.MapsTo addr (true,g) cm ->
          g.(tag_unspecified) = false ->
          (forall bs, fetch_bytes bm addr (sizeof_pointer MorelloImpl.get) = bs ->
                 (exists c,
                     (* decode without error *)
                     decode_cap bs true c
                     (* with decoded bounds bounds fitting one of the allocations *)
                     /\ (exists a alloc_id, ZMap.M.MapsTo alloc_id a am /\
                                        (* We do not allow escaped pointers to local variables *)
                                        cap_bounds_within_alloc c a)
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
      apply ZMap.F.empty_mapsto_iff in H;
        contradiction.
    -
      intros alloc_id1 alloc_id2 a1 a2 NA H H0.
      apply ZMap.F.empty_mapsto_iff in H;
        contradiction.
    -
      intros k a H.
      apply ZMap.F.empty_mapsto_iff in H.
      tauto.
    -
      unfold AMapProofs.map_forall_keys.
      intros k H.
      apply AMap.F.empty_in_iff in H;
        contradiction.
    -
      intros alloc_id H.
      apply ZMap.F.empty_in_iff in H.
      tauto.
    -
      intros k a H.
      apply ZMap.F.empty_mapsto_iff in H.
      tauto.
    -
      intros addr g H bs H0.
      apply AMap.F.empty_mapsto_iff in H;
        contradiction.
  Qed.

  Lemma mem_state_after_ghost_tags_preserves:
    forall m addr size,
      AddressValue.to_Z addr + Z.of_nat size <= AddressValue.ADDR_LIMIT ->
      mem_invariant m ->
      mem_invariant (mem_state_with_capmeta
                       (init_ghost_tags addr size (capmeta m))
                       m).
  Proof.
    intros m addr sz L H.
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
      apply AMapProofs.map_in_mapsto in E.
      destruct E as [tg E].
      unfold mem_state_with_capmeta in E.
      simpl in E.
      apply init_ghost_tags_spec in E.
      +
        destruct E.
        *
          (* capmeta unchanged at [a] *)
          apply AMapProofs.map_mapsto_in in H.
          apply Balign.
          apply H.
        *
          (* capmeta cleared *)
          destruct H as [H1 H2].
          apply H1.
      +
        apply L.
    -
      intros a g E bs F.
      simpl in *.
      apply init_ghost_tags_spec in E.
      +
        destruct E as [E | [A E]].
        *
          (* capmeta unchanged at [a] *)
          specialize (MIcap a g E bs F).
          apply MIcap.
        *
          inversion E.
      +
        apply L.
  Qed.

  Instance allocator_PreservesInvariant
    (size: nat)
    (align: Z)

    (is_dynamic: bool)
    (pref: CoqSymbol.prefix)
    (ty: option CoqCtype.ctype)
    (ro_status: readonly_status):

    (0<align) ->
    forall s,
      PreservesInvariant mem_invariant s (allocator size align is_dynamic pref ty ro_status).
  Proof.
    intros AP s.
    unfold allocator.
    preserves_step.
    break_if.
    preserves_step.
    break_if.
    preserves_step.
    preserves_step.
    2: preserves_step.

    apply put_PreservesInvariant'.
    intros H.

    bool_to_prop_hyp.

    (* These are used in different proof branches below *)
    pose proof (AddressValue.to_Z_in_bounds (last_address s)) as LB.

    pose proof (Zdiv.Z_mod_lt (AddressValue.to_Z (last_address s) - Z.of_nat size) align) as LM.
    autospecialize LM. lia.


    destruct H as [MIbase MIcap].
    destruct_base_mem_invariant MIbase.
    split.
    -
      (* base *)
      repeat split;cbn.
      + (* Bdead *)
        apply ZMapProofs.map_forall_add;auto.
      + (* Bnooverlap *)
        intros alloc_id1 alloc_id2 a1 a2 H H0 H1.
        specialize (Bnooverlap alloc_id1 alloc_id2 a1 a2 H).

        apply ZMap.F.add_mapsto_iff in H0,H1.
        destruct H0 as [[H0k H0v]|[H0n H0m]], H1 as [[H1k H1v]|[H1n H1m]].
        * (* next_alloc_id s = alloc_id1 = alloc_id2 *)
          congruence.
        *
          (* [a1] is new, [a2] exists *)
          clear MIcap Bnooverlap.
          subst a1.
          specialize (Blastaddr alloc_id2 a2 H1m). cbn in Blastaddr.
          specialize (Bfit alloc_id2 a2 H1m). cbn in Bfit.
          specialize (Bnextallocid alloc_id2).
          autospecialize Bnextallocid.
          {
            eapply ZMapProofs.map_mapsto_in.
            eauto.
          }
          cbn in Bnextallocid.

          unfold allocations_do_no_overlap.
          cbn.
          left.
          rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
            lia).
          lia.
        *
          (* [a2] is new, [a1] exists *)
          clear MIcap Bnooverlap.
          subst a2.
          specialize (Blastaddr alloc_id1 a1 H0m). cbn in Blastaddr.
          specialize (Bfit alloc_id1 a1 H0m). cbn in Bfit.
          specialize (Bnextallocid alloc_id1).
          autospecialize Bnextallocid.
          {
            eapply ZMapProofs.map_mapsto_in.
            eauto.
          }
          cbn in Bnextallocid.

          unfold allocations_do_no_overlap.
          cbn.
          right.
          left.
          rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
                                                  lia).
          lia.
        * (* both allocations already exist *)
          auto.
      + (* Bfit *)
        clear MIcap.
        apply ZMapProofs.map_forall_add;auto.
        cbn.
        rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
                                                lia).
        lia.
      + (* Balign *)
        apply mem_state_after_ghost_tags_preserves.
        --
          rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
                                                  lia).
          lia.
        --
          repeat split;auto.
      + (* Bnextallocid *)
        apply ZMapProofs.map_forall_keys_add;[|lia].
        intros k H.
        specialize (Bnextallocid k H). cbn in Bnextallocid.
        lia.
      + (* Blastaddr *)
        clear MIcap.
        apply ZMapProofs.map_forall_add;cbn.
        *
          intros k v H.
          rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
            lia).
          specialize (Blastaddr k v H).
          cbn in Blastaddr.
          lia.
        *
          lia.
    -
      cbn.
      intros addr g H U bs F.
      apply init_ghost_tags_spec in H.
      destruct H.
      +
        (* existing *)
        specialize (MIcap addr g H U bs F).
        destruct MIcap as [c [M1 [a [alloc_id [M2 M3]]]]].
        exists c.
        split;[assumption|].
        exists a, alloc_id.
        split;[|assumption].
        eapply ZMap.M.add_2.
        specialize (Bnextallocid alloc_id).
        autospecialize Bnextallocid.
        {
          eapply ZMapProofs.map_mapsto_in.
          eauto.
        }
        cbn in Bnextallocid.
        lia.
        apply M2.
      +
        inv H.
        inv H1.
      +
        rewrite AddressValue.of_Z_roundtrip by (unfold AddressValue.ADDR_MIN in *;
                                                lia).
        lia.
  Qed.
  Opaque allocator.

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
    (addr: AddressValue.t)
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
    (addr : AddressValue.t)
    (bm: AMap.M.t (option ascii))
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
        forall (s' : mem_state) (x : AMap.M.t (bool * CapGhostState)),
          AMap.map_mmapi (maybe_revoke_pointer a m) (capmeta m) s = (s', inr x) -> mem_invariant s'.
  Proof.
    intros a m IM s IS s' x M.

    pose proof (amap_mmapi_PreservesInvariant mem_invariant (maybe_revoke_pointer a m) (capmeta m) s) as P.
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
    (k : AddressValue.t)
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

  Instance amap_mmapi_maybe_revoke_pointer_same_state
    (a: allocation)
    (m: mem_state)
    (oldmeta : AMap.M.t (bool * CapGhostState)):
    SameState (AMap.map_mmapi (maybe_revoke_pointer a m) oldmeta).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma amap_mmapi_maybe_revoke_pointer_spec
    (a : allocation)
    (s : mem_state)
    (oldmeta newmeta : AMap.M.t (bool * CapGhostState)):
    AMap.map_mmapi (maybe_revoke_pointer a s) oldmeta s = (s, inr newmeta) ->
    AMapProofs.map_relate_keys oldmeta newmeta (fun addr : AMap.M.key => revoked_pointer_rel a addr s.(bytemap)).
  Proof.
    intros H.
    intros k.
    unfold AMap.map_mmapi in H.
    unfold AMap.map_sequence in H.
    break_let.
    remember (AMap.M.mapi (maybe_revoke_pointer a s) oldmeta) as newmeta'.

    assert(AMapProofs.map_relate_keys newmeta' newmeta
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
      remember (AMap.M.mapi (maybe_revoke_pointer a s) oldmeta) as newmeta.

      rename l into rescaps, Heqp0 into SEQ, Heqp into SPL.
      remember (AMap.M.elements (elt:=memM (bool * CapGhostState)) newmeta) as enewmeta eqn:E.
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
        destruct (@AMap.F.In_dec _ newmeta k) as [I|NI].
        +
          (* key originally exists *)
          left.
          apply AMapProofs.map_in_mapsto in I.
          destruct I as [v1 I].
          exists v1.

          assert(AMap.M.MapsTo k v1 newmeta) as I1 by assumption.
          rewrite Heqnewmeta in I1.
          apply AMap.F.mapi_inv in I1.
          destruct I1 as [v2 [k' [I3 [I4 I5]]]].
          subst k'.

          pose proof (AMap.M.elements_1 I) as H.
          rewrite <- E in H.
          apply InA_alt in H.
          destruct H as [(addr,v2') [H1 H2]].

          unfold AMap.M.eq_key_elt, ZMap.M.Raw.Proofs.PX.eqke in H1.
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
            apply AMap.P.of_list_1.
            --
              apply AMapProofs.map_combine_eq_key_NoDupA.
              pose proof (AMap.M.elements_3w newmeta) as NDM.
              pose proof (AMapProofs.split_eq_key_NoDup _ _ _ SPL).
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
                unfold memM, ZMap.M.key in *.
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
          pose proof (AMap.M.elements_3w newmeta) as NDM.
          pose proof (AMapProofs.split_eq_key_NoDup _ _ _ SPL).
          rewrite E in H.
          specialize (H NDM).
          intros C.
          destruct C as [v C].
          apply AMap.P.of_list_1 in C;[|apply AMapProofs.map_combine_eq_key_NoDupA, H].
          apply AMapProofs.InA_eq_key_combine in C.
          contradict NI.
          clear - E SPL C NDM.
          subst enewmeta.
          replace lk with (fst (split (AMap.M.elements (elt:=memM (bool * CapGhostState)) newmeta))) in C.
          apply AMapProofs.In_zmap_elements_split_zmap_in, C.
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

        assert (AMap.M.MapsTo addr v1 newmeta).
        {
          apply lookup_elements_MapsTo.
          exists k.
          rewrite E in ES.
          apply ES.
        }
        rewrite Heqnewmeta in H0.
        apply AMap.F.mapi_inv in H0.
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
    pose proof (AMapProofs.map_relate_keys_same_keys _ _ _ N k) as SN.
    destruct (@AMap.F.In_dec _ oldmeta k) as [I|NI].
    -
      (* key originally exists *)
      left.
      apply AMapProofs.map_in_mapsto in I.
      destruct I as [v1 I].
      exists v1.
      pose proof (@AMap.M.mapi_1 _ _ _ _ _ (maybe_revoke_pointer a s) I) as [y [YH Z]].
      subst y.
      rewrite <- Heqnewmeta' in Z.
      specialize (N k).
      destruct N as [N|[NN1 NN2]].
      +
        destruct N as [v1' [v2 [N1 [N2 N3]]]].
        apply (AMap.F.MapsTo_fun N1) in Z.
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
      assert(~ (exists v : bool * CapGhostState, AMap.M.MapsTo k v oldmeta)) as NM.
      intros [v C].
      apply AMapProofs.map_mapsto_in in C.
      congruence.
      split;[apply NM|].
      intros [v C].
      apply AMapProofs.map_mapsto_in in C.
      apply SN in C.
      contradict NM.
      clear - C Heqnewmeta'.
      subst.
      apply AMap.M.mapi_2 in C.
      apply C.
  Qed.

  (* This function stands out because its state is subtly but deeply
     connected to the return value. We couldn't use our usual
     preservation step lemmas and had to resort to brute-forcing our
     way through.  *)
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
      eapply amap_mmapi_maybe_revoke_pointer_same_state.
      eauto.
    }
    subst m.

    apply(amap_mmapi_maybe_revoke_pointer_spec a s (capmeta s) newmeta) in Heqp0.
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
        eapply AMapProofs.map_mapsto_in.
        eauto.
      +
        contradict NR1.
        eapply AMapProofs.map_in_mapsto in I.
        apply I.
    -
      clear Bdead Bnooverlap Balign.
      intros addr g H1 U bs H0.
      specialize (Scap addr g).
      specialize (R addr).
      cbn in *.
      destruct R as [[v1 [v2 [M1 [M2 R]]]]|[NR0 NR1]].
      --
        pose proof (AMap.F.MapsTo_fun M2 H1).
        subst v2.
        (* both keys present *)
        invc R.
        ++
          (* ghost states are same *)
          specialize (Scap M1 U).
          remember (fetch_bytes bytemap0 addr (sizeof_pointer MorelloImpl.get)) as bs.
          specialize (Scap bs).
          autospecialize Scap.
          reflexivity.
          auto.
        ++
          (* revoked *)
          specialize (Scap M1 U).
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
    (addr : AMap.M.key)
    (g : CapGhostState)
    (bs : list (option ascii))
    (c : Capability_GS.t)
    :
    revoke_pointers alloc s = (s', inr tt) ->
    AMap.M.MapsTo addr (true, g) (capmeta s') ->
    fetch_bytes (bytemap s') addr (sizeof_pointer MorelloImpl.get) = bs ->
    decode_cap bs true c -> ~ cap_bounds_within_alloc c alloc.
  Proof.
    intros R M F D.
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

    pose proof (amap_mmapi_maybe_revoke_pointer_same_state _ _ _ _ _ _ Heqp) as E.
    subst m.

    apply update_state_capmeta in Heqp0.
    destruct Heqp0 as [E1 E2].
    subst.
    generalize dependent (capmeta s').
    intros cm Z M.

    apply amap_mmapi_maybe_revoke_pointer_spec in Z.
    specialize (Z addr).
    invc Z.
    -
      (* both exists in [campeta s] and [cm] *)
      destruct H as [g1 [g2 [H1 [H2 R]]]].
      pose proof (AMap.F.MapsTo_fun M H2).
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
    (AM: ZMap.M.MapsTo alloc_id alloc (allocations s))
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
        apply ZMap.M.remove_3 in H.
        eapply Bdead;eauto.
      +
        intros alloc_id1 alloc_id2 a1 a2 NA H H0.
        apply ZMap.M.remove_3 in H0, H.
        eapply Bnooverlap.
        eauto.
        eauto.
        eauto.
      +
        apply ZMapProofs.map_forall_remove.
        auto.
      +
        apply Balign.
      +
        intros alloc_id' H.
        destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
        *
          apply (ZMap.M.remove_1 E) in H.
          inv H.
        *
          rewrite (ZMap.F.remove_neq_in_iff _ NE) in H.
          eauto.
      +
        apply ZMapProofs.map_forall_remove.
        auto.
    -
      clear ISbase'.
      intros addr g A U bs F.
      specialize (IScap' addr g A U bs F).
      destruct IScap' as [c [IScap3' [alloc' [alloc_id' [IScap4' IScap5']]]]].
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
          apply amap_mmapi_maybe_revoke_pointer_same_state in Heqp.
          subst m.
          subst s0.
          destruct s.
          cbn in *.
          tuple_inversion.
          cbn in *.
          eapply ZMap.F.MapsTo_fun; eauto.
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
        apply ZMap.M.remove_2;auto.
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
    rewrite resolve_has_INSTANT.
    destruct ptr eqn:P; intros.
    1: preserves_steps.
    break_match_goal;cbn;[preserves_step|].

    apply bind_PreservesInvariant_full.
    intros H s' x H0.
    pose proof (find_live_allocation_SameState (Capability_GS.cap_get_value t)) as H2.
    specialize (H2 _ _ _ H0).
    subst s'.
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
        unfold execErrS in Heqs1.
        break_let.
        tuple_inversion.
        inl_inr.
      +
        unfold execErrS in Heqs1.
        break_let.
        tuple_inversion.
        inl_inr_inv.
        subst m.
        destruct x0.
        rename a into alloc, s0 into alloc_id.
        apply find_live_allocation_res_consistent in Heqp.
        (* It looks like we have everything we need here *)
        unfold post_exec_invariant, lift_sum_p.
        break_match_goal;[trivial|].

        unfold execErrS in Heqs0.
        break_let.
        break_match_hyp;[inl_inr|inl_inr_inv].
        subst.
        destruct u.
        eapply remove_revoked_allocation_preserves; eauto.
      +
        apply A.
      +
        apply fail_PreservesInvariant, A.
      +
        apply fail_PreservesInvariant, A.
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

  Instance compare_ptrval_SameState
    (label: string)
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) :
    SameState (compare_ptrval label loc ptr1 ptr2).
  Proof.
    unfold compare_ptrval.
    same_state_steps.
  Qed.

  Instance lt_ptrval_SameState
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) :
    SameState (lt_ptrval loc ptr1 ptr2).
  Proof.
    unfold lt_ptrval.
    same_state_steps.
  Qed.

  Instance gt_ptrval_SameState
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) :
    SameState (gt_ptrval loc ptr1 ptr2).
  Proof.
    unfold gt_ptrval.
    same_state_steps.
  Qed.

  Instance le_ptrval_SameState
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) :
    SameState (le_ptrval loc ptr1 ptr2).
  Proof.
    unfold le_ptrval.
    same_state_steps.
  Qed.

  Instance ge_ptrval_SameState
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) :
    SameState (ge_ptrval loc ptr1 ptr2).
  Proof.
    unfold ge_ptrval.
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
    apply SameStatePreserves, find_cap_allocation_SameState.

    subst.
    remember (ZMap.map_update _ _ _) as newallocations.
    unfold mem_state_with_allocations.
    destruct H as [MIbase MIcap].
    destruct_base_mem_invariant MIbase.
    split.
    -
      (* base invariant *)
      clear MIcap.
      repeat split;cbn.
      +
        (* Bdead *)
        clear - Bdead Heqnewallocations.
        generalize dependent (allocations s').
        clear s'.
        intros old Bdead Heqnewallocations alloc_id a H.
        rename s0 into alloc_id'.
        subst.
        destruct (Z.eq_dec alloc_id alloc_id').
        *
          specialize (Bdead alloc_id).
          subst alloc_id'.
          destruct (ZMap.M.find alloc_id old) eqn:F.
          --
            apply ZMap.M.find_2 in F.
            specialize (Bdead a0 F).
            pose proof (ZMapProofs.map_update_MapsTo_update_at_k F H).
            clear H F.
            cbn in H0.
            invc H0.
            cbn.
            assumption.
          --
            apply ZMap.F.not_find_in_iff in F.
            clear Bdead.
            pose proof (ZMapProofs.map_update_MapsTo_new_at_k F H).
            clear H F.
            cbn in H0.
            inversion H0.
        *
          apply ZMapProofs.map_update_MapsTo_not_at_k in H;auto.
          eapply Bdead; eauto.
      +
        (* Bnooverlap *)
        clear Bfit Bdead Balign Bnextallocid Blastaddr.
        generalize dependent (allocations s').
        clear s'.
        intros old Bnooverlap Heqnewallocations alloc_id1 alloc_id2 a1 a2 NA M1 M2.
        rename s0 into alloc_id.
        subst.

        Ltac solve_cases :=
          repeat match goal with
            (* absurd cases *)
            | [H: ZMap.M.find ?alloc_id _ = None, M: ZMap.M.MapsTo ?alloc_id _ _ |- _]
              =>
                let X := fresh "X" in
                apply ZMap.F.not_find_in_iff in H;
                pose proof (ZMapProofs.map_update_MapsTo_new_at_k H M) as X;
                cbn in X; inversion X
            | [H: ZMap.M.find ?alloc_id _ = Some _, M: ZMap.M.MapsTo ?alloc_id _ _ |- _]
              =>
                let X := fresh "X" in
                apply ZMap.M.find_2 in H;
                pose proof (ZMapProofs.map_update_MapsTo_update_at_k H M) as X;
                cbn in X;
                clear M;
                some_inv
            | [H:  ?alloc_id' <> ?alloc_id, M: ZMap.M.MapsTo ?alloc_id' _ (ZMap.map_update ?alloc_id _ _) |- _]
              =>
                apply ZMapProofs.map_update_MapsTo_not_at_k in M;auto
            end.

        destruct (Z.eq_dec alloc_id1 alloc_id), (Z.eq_dec alloc_id2 alloc_id),
          (ZMap.M.find alloc_id1 old) eqn:F1, (ZMap.M.find alloc_id2 old) eqn:F2; subst ; try solve_cases.

        all:
          unfold allocations_do_no_overlap in *;
          unfold allocation_with_prefix;
          cbn; eauto.
      +
        (* Bfit *)
        (* Blastaddr *)
        clear - Bfit Heqnewallocations.
        subst newallocations.
        rename s0 into alloc_id'.
        intros alloc_id a.
        destruct (Z.eq_dec alloc_id alloc_id') as [E|NE].
        *
          subst alloc_id'.
          intros H.
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply ZMap.M.find_2 in Heqo0.
            apply ZMap.F.add_mapsto_iff in H.
            destruct H;[|destruct H; congruence].
            destruct H as [_ H3].
            subst a0.
            specialize (Bfit alloc_id a1 Heqo0).
            unfold allocation_with_prefix in H1.
            destruct a.
            cbn in *.
            invc H1.
            auto.
          --
            apply ZMapProofs.map_mapsto_in in H.
            apply ZMap.M.remove_1 in H.
            tauto.
            reflexivity.
        *
          intros H.
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply ZMap.F.add_neq_mapsto_iff in H; auto.
            apply ZMap.F.remove_neq_mapsto_iff in H; auto.
            eauto.
          --
            apply ZMap.F.remove_neq_mapsto_iff in H; auto.
            eauto.
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
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply Bnextallocid.
            apply ZMap.F.in_find_iff.
            rewrite Heqo0.
            auto.
          --
            apply ZMap.M.remove_1 in H.
            tauto.
            reflexivity.
        *
          intros H.
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply Bnextallocid.
            apply ZMap.F.add_neq_in_iff in H;auto.
            apply ZMap.F.remove_neq_in_iff in H;auto.
          --
            apply ZMap.F.remove_neq_in_iff in H;auto.
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
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply ZMap.M.find_2 in Heqo0.
            apply ZMap.F.add_mapsto_iff in H.
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
            apply ZMapProofs.map_mapsto_in in H.
            apply ZMap.M.remove_1 in H.
            tauto.
            reflexivity.
        *
          intros H.
          unfold ZMap.map_update in H.
          repeat break_match_hyp;try some_none; try some_inv.
          --
            apply ZMap.F.add_neq_mapsto_iff in H; auto.
            apply ZMap.F.remove_neq_mapsto_iff in H; auto.
            eauto.
          --
            apply ZMap.F.remove_neq_mapsto_iff in H; auto.
            eauto.
    -
      rename c into ty, s0 into alloc_id.
      clear Bdead Bnooverlap Balign.
      cbn.
      intros addr g H U bs H0.
      specialize (MIcap addr g H U bs H0).
      destruct MIcap as [c [D [a' [alloc_id' [M B]]]]].
      exists c.
      split;[assumption|].
      destruct (Z.eq_dec alloc_id alloc_id').
      +
        subst alloc_id'.
        subst newallocations.
        epose proof (ZMapProofs.map_update_MapsTo_update_at_k' M).
        eexists.
        eexists.
        split.
        eapply H1.
        eauto.
        eauto.
      +
        subst newallocations.
        eapply ZMapProofs.map_update_MapsTo_not_at_k in M.
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

  Instance allocate_object_PreservesInvariantg
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
    break_if;[preserves_step|].
    preserves_step.
    preserves_step.
    preserves_step.
    -
      break_match_goal; repeat break_let.
      +
        (* with init *)
        apply bind_PreservesInvariant_value.
        intros H s'0 x0 H0.


        assert(mem_invariant s'0) as S0.
        {
          pose proof (allocator_PreservesInvariant (Z.to_nat (Capability_GS.representable_length (Z.of_nat x)))
                        (Z.max (num_of_int int_val)
                           (1 +
                              AddressValue.to_Z
                                (AddressValue.bitwise_complement
                                   (AddressValue.of_Z
                                      (Capability_GS.representable_alignment_mask (Z.of_nat x))))))
                        false pref (Some ty) r
            ) as A.
          autospecialize A.
          lia.
          specialize (A s' H).
          unfold post_exec_invariant, lift_sum_p in A.
          clear Heqp.
          break_match_hyp.
          --
            unfold execErrS in Heqs0.
            break_let.
            tuple_inversion.
            invc Heqs0.
          --
            unfold execErrS in Heqs0.
            break_let.
            tuple_inversion.
            apply ret_inr in Heqs0.
            invc Heqs0.
            assumption.
        }

        split.
        *
          apply S0.
        *
          repeat break_let.
          preserves_step.
          preserves_step.
          preserves_step.
          repeat break_let.
          preserves_step;[|preserves_step].
          preserves_step.

          bool_to_prop_hyp.
          destruct x1, p0.
          tuple_inversion.

          (* TODO: need `allocator_capmeta_spec`
             similar to `init_ghost_tags_spec`
           *)

          (* TODO: this whole branch maybe unecessary in view of this pending change:
             https://github.com/rems-project/cerberus/issues/229
           *)
          admit.
      +
        (* No init *)
        preserves_step.
        apply allocator_PreservesInvariant.
        lia.
        break_let.
        preserves_step.
    -
      repeat break_let.
      preserves_step.
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
    preserves_steps.
    apply allocator_PreservesInvariant.
    bool_to_prop_hyp.
    lia.
  Qed.

  Definition memcpy_alloc_bounds_check_p
    (c1 c2: Capability_GS.t)
    (alloc1 alloc2: allocation)
    (sz:Z)
    : Prop
    :=
    let ptr1_base := cap_to_Z c1 in
    let ptr1_limit := ptr1_base + sz in
    let alloc1_base := AddressValue.to_Z alloc1.(base) in
    let alloc1_limit := alloc1_base + Z.of_nat alloc1.(size) in

    let ptr2_base := cap_to_Z c2 in
    let ptr2_limit := ptr2_base + sz in
    let alloc2_base := AddressValue.to_Z alloc2.(base) in
    let alloc2_limit := alloc2_base + Z.of_nat alloc2.(size) in

    ptr1_base >= alloc1_base
    /\ ptr1_limit <= alloc1_limit
    /\ ptr2_base  >= alloc2_base
    /\ ptr2_limit <= alloc2_limit
    /\ Z.abs (ptr1_base-ptr2_base) >= sz.

  Inductive mempcpy_args_sane: ZMap.M.t allocation -> pointer_value -> pointer_value -> Z -> Prop
    :=
  | mempcpy_args_sane_P: forall allocations c1 c2 sz alloc_id1 alloc_id2 alloc1 alloc2,
      0 <= sz ->
      ZMap.M.MapsTo alloc_id1 alloc1 allocations ->
      ZMap.M.MapsTo alloc_id2 alloc2 allocations ->
      alloc1.(is_dead) = false ->
      alloc2.(is_dead) = false ->
      cap_bounds_within_alloc c1 alloc1 ->
      cap_bounds_within_alloc c2 alloc2 ->
      memcpy_alloc_bounds_check_p c1 c2 alloc1 alloc2 sz ->
      mempcpy_args_sane allocations (PVconcrete c1) (PVconcrete c2) sz.

  (* Copying pointer from `addr2` to `addr1` in capmeta
     preserves invariant *)
  Fact copy_pointer_PreservesInvariant
    {addr1 addr2 : AddressValue.t}
    {m : mem_state_r}
    {p : bool * CapGhostState}:
    mem_invariant m ->
    AMap.M.find addr2 (capmeta m) = Some p ->
    is_pointer_algined addr1 = true ->
    (fetch_bytes (bytemap m) addr1 (sizeof_pointer MorelloImpl.get)  =
       fetch_bytes (bytemap m) addr2 (sizeof_pointer MorelloImpl.get))
    ->
      mem_invariant (mem_state_with_capmeta (AMap.M.add addr1 p (capmeta m)) m).
  Proof.
    intros H F A B.
    destruct H as [MIbase MIcap].
    unfold mem_invariant.
    split.
    -
      (* base *)
      clear MIcap.
      destruct_base_mem_invariant MIbase.
      repeat split; auto.
      cbn.
      unfold ZMapProofs.map_forall_keys, AMapProofs.map_forall_keys in *.
      intros k H.
      destruct (AddressValue_as_OT.eq_dec k addr1) as [E|NE].
      +
        subst.
        unfold is_pointer_algined in A.
        unfold addr_ptr_aligned.
        lia.
      +
        apply AMap.F.add_neq_in_iff in H;auto.
    -
      clear MIbase A.
      destruct (AddressValue_as_OT.eq_dec addr1 addr2) as [E|NE].
      +
        subst addr2.
        cbn in *.
        intros k.
        destruct (AddressValue_as_OT.eq_dec k addr1) as [KE|KNE].
        *
          subst addr1.
          intros g H bs H0.
          apply AMap.F.find_mapsto_iff in F.
          apply AMap.F.add_mapsto_iff in H.
          destruct H.
          --
            destruct H as [_ P].
            subst p.
            specialize (MIcap k g F bs H0).
            auto.
          --
            destruct H.
            congruence.
        *
          intros g H bs H0.
          apply AMap.F.find_mapsto_iff in F.
          apply AMap.M.add_3 in H;[|auto].
          specialize (MIcap k g H bs H0).
          auto.
      +
        intros k g H U bs H0.
        cbn in *.

        destruct (AddressValue_as_OT.eq_dec k addr1) as [KE1|KNE1].
        *
          subst addr1.
          apply AMap.F.find_mapsto_iff in F.
          apply AMap.F.add_mapsto_iff in H.
          destruct H.
          --
            destruct H as [_ P].
            subst p.
            rewrite B in H0.
            specialize (MIcap addr2 g F U bs H0).
            auto.
          --
            destruct H.
            congruence.
        *
          apply AMap.M.add_3 in H;[|auto].
          --
            apply AMap.M.find_2 in F.
            destruct (AddressValue_as_OT.eq_dec k addr2) as [KE|KNE].
            ++
              subst addr2.
              specialize (MIcap k).
              pose proof (AMap.F.MapsTo_fun F H) as E.
              subst p.
              clear H.
              specialize (MIcap g F U bs).
              auto.
            ++
              specialize (MIcap k g H U bs H0).
              destruct MIcap as [c [M2 [a [alloc_id [M3 M4]]]]].
              exists c.
              split.
              assumption.
              exists a, alloc_id.
              split.
              assumption.
              assumption.
  Qed.

  Instance memcpy_args_check_SameState
    (loc:location_ocaml)
    (p1 p2: pointer_value_indt)
    (n:Z ):
    SameState (memcpy_args_check loc p1 p2 n).
  Proof.
    unfold memcpy_args_check, memcpy_alloc_bounds_check.
    same_state_steps.
  Qed.

  Fact find_cap_allocation_st_spec
    (s : mem_state_r)
    (c : Capability_GS.t)
    (sid : storage_instance_id)
    (a : allocation)
    :
    find_cap_allocation_st s c = Some (sid, a) ->
    ZMap.M.find (elt:=allocation) sid (allocations s) = Some a
    /\ a.(is_dead) = false
    /\ cap_bounds_within_alloc c a.
  Proof.
    intros H.
    unfold find_cap_allocation_st in H.
    break_let.
    repeat rewrite resolve_has_any_PNVI_flavour in H.
    apply ZMapProofs.map_find_first_exists in H.
    destruct H as [H1 H2].
    repeat split.
    - assumption.
    -
      bool_to_prop_hyp.
      apply negb_true_iff.
      auto.
    -
      bool_to_prop_hyp.
      rewrite Heqp.
      cbn.
      lia.
    -
      bool_to_prop_hyp.
      rewrite Heqp.
      cbn.
      lia.
  Qed.

  Fact eff_array_shift_ptrval_uchar_spec
    (loc : location_ocaml)
    (c : Capability_GS.t)
    (n : Z)
    (s: mem_state)
    :
    forall v,
      eff_array_shift_ptrval loc (PVconcrete c) CoqCtype.unsigned_char (IV n) s =  (s, inr v) ->
      v =
        (PVconcrete
           (Capability_GS.cap_set_value c (AddressValue.with_offset (Capability_GS.cap_get_value c) n))
        ).
  Proof.
    intros ptrval H.
    Transparent serr2InternalErr bind raise ret get fail fail_noloc.
    unfold eff_array_shift_ptrval, serr2InternalErr, option2serr, raise, bind, ret, Exception_serr, Exception_errS, Exception_either, memM_monad, Monad_errS, Monad_either in H.
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


  Fact repr_char_bytes_size_helper
    (fuel : nat)
    (funptrmap0 funptrmap' : ZMap.M.t (digest * string * Capability_GS.t))
    (capmeta0 capmeta' : AMap.M.t (bool * CapGhostState))
    (addr : AddressValue.t)
    (iv: integer_value_indt)
    (bs : list (option ascii)):
    repr fuel funptrmap0 capmeta0 addr (MVinteger (CoqIntegerType.Unsigned CoqIntegerType.Ichar) iv) =
      inr (funptrmap', capmeta', bs) -> Datatypes.length bs = 1%nat.
  Proof.
    intros R.
    unfold repr in R.
    destruct fuel;[apply raise_either_inr_inv in R;tauto|].
    break_match_hyp.
    -
      state_inv_step.
      break_match_hyp.
      apply raise_either_inr_inv in R3; tauto.
      rewrite MorelloImpl.uchar_size in R4.
      cbn in R4.
      apply ret_inr in R4.
      invc R4.
      match goal with
      | [H: monadic_list_init _ ?f = _ |- _] => generalize dependent f;intros
      end.
      cbn in R3.
      state_inv_step.
      reflexivity.
    -
      apply raise_either_inr_inv in R; tauto.
  Qed.

  Fact repr_char_bytes_size_unspec_helper
    (fuel : nat)
    (funptrmap0 funptrmap' : ZMap.M.t (digest * string * Capability_GS.t))
    (capmeta0 capmeta' : AMap.M.t (bool * CapGhostState))
    (addr : AddressValue.t)
    (l an: list CoqAnnot.annot)
    (bs : list (option ascii))
    (ty: CoqCtype.ctype):

    (ty = (CoqCtype.Ctype l (CoqCtype.Atomic (CoqCtype.Ctype an (CoqCtype.Basic (CoqCtype.Integer (CoqIntegerType.Unsigned CoqIntegerType.Ichar))))))
     \/ ty = (CoqCtype.Ctype l (CoqCtype.Basic (CoqCtype.Integer (CoqIntegerType.Unsigned CoqIntegerType.Ichar)))))
    ->
      repr fuel funptrmap0 capmeta0 addr (MVunspecified ty) = inr (funptrmap', capmeta', bs) -> Datatypes.length bs = 1%nat.
  Proof.
    intros T P.
    unfold repr in P.
    destruct fuel;[apply raise_either_inr_inv in P;tauto|].
    destruct T;
      (state_inv_step;
       rewrite MorelloImpl.uchar_size in P0;
       cbn in P0;
       apply ret_inr in P0;
       invc P0;
       apply repeat_length).
  Qed.

  (* Probably need to generalize in future for all types via `sizeof` *)
  Lemma repr_char_bytes_size
    (fuel: nat)
    (funptrmap funptrmap': ZMap.M.t (digest * string * Capability_GS.t))
    (capmeta capmeta': AMap.M.t (bool*CapGhostState))
    (addr : AddressValue.t)
    (m : mem_value)
    (bs: list (option ascii))
    (mt : CoqCtype.ctype)
    (an: list CoqAnnot.annot):
    typeof m = inr mt ->
    CoqCtype.unatomic mt =
      CoqCtype.Ctype an (CoqCtype.Basic (CoqCtype.Integer (CoqIntegerType.Unsigned CoqIntegerType.Ichar))) ->
    repr fuel funptrmap capmeta addr m = inr (funptrmap', capmeta', bs) ->
    length bs = 1%nat.
  Proof.
    intros T U R.
    unfold CoqCtype.unatomic in U.
    destruct mt.

    destruct c; try discriminate.
    -
      invc U.
      destruct m;
        try
          (cbn in T;
           rewrite bind_of_return in T;[|typeclasses eauto];
           apply ret_inr in T;
           inl_inr_inv).
      +
        cbn in T.
        destruct c.
        rewrite bind_of_return in T;[|typeclasses eauto].
        apply ret_inr in T.
        inl_inr_inv.
        subst.
        revert R.
        apply repr_char_bytes_size_unspec_helper with (l:=l) (an:=l).
        auto.
      +
        subst.
        eapply repr_char_bytes_size_helper;eauto.
      +
        cbn in T.
        destruct l.
        *
          Transparent raise.
          unfold raise, Exception_either in T.
          state_inv_step.
          Opaque raise.
        *
          state_inv_step.
    -
      destruct m;
        try
          (cbn in T;
           rewrite bind_of_return in T;[|typeclasses eauto];
           apply ret_inr in T;
           inl_inr_inv).
      +
        cbn in T.
        destruct c0.
        rewrite bind_of_return in T;[|typeclasses eauto].
        apply ret_inr in T.
        inl_inr_inv.
        subst.
        revert R.
        apply repr_char_bytes_size_unspec_helper with (l:=l0) (an:=an).
        auto.
      +
        cbn in T.
        destruct l0.
        *
          Transparent raise.
          unfold raise, Exception_either in T.
          state_inv_step.
          Opaque raise.
        *
          state_inv_step.
  Qed.

  Lemma store_other_spec
    (loc : location_ocaml)
    (c : Capability_GS.t)
    (s s' : mem_state)
    (m : mem_value)
    (fp : footprint)
    (addr : AddressValue.t):
    Capability_GS.cap_get_value c = addr ->
    store loc CoqCtype.unsigned_char false (PVconcrete c) m s = (s', inr fp) ->
    forall addr' : AMap.M.key, addr' <> addr -> AMap.M.find (elt:=(option ascii)) addr' (bytemap s') = AMap.M.find (elt:=(option ascii)) addr' (bytemap s).
  Proof.
    intros CV ST addr' NE.
    Opaque repr.
    unfold store in ST.
    unfold sizeof in ST.
    cbn in ST.
    rewrite MorelloImpl.uchar_size in ST.
    cbn in ST.
    state_inv_step.

    assert(length l = 1%nat) as L by (eapply repr_char_bytes_size;eauto).
    apply AMapProofs.map_add_list_not_at; auto.
  Qed.

  (* Non-locking store does not change allocations.

     Probably could be generalized for other types, this is all we
     need for now.  *)
  Fact store_char_preserves_allocations:
    forall (loc : location_ocaml) (p1:pointer_value)
           (s0 : mem_state) (s : mem_state_r) (v1 : mem_value) (fp : footprint),
      store loc CoqCtype.unsigned_char false
        p1 v1 s =
        (s0, inr fp)
      -> allocations s0 = allocations s.
  Proof.
    intros loc p1 s0 s v1 fp ST.
    Opaque repr.
    unfold store in ST.
    unfold sizeof in ST.
    cbn in ST.
    rewrite MorelloImpl.uchar_size in ST.
    cbn in ST.
    state_inv_step; reflexivity.
    Transparent repr.
  Qed.

  Fact memcpy_alloc_bounds_check_p_c_bounds
    (sz : Z)
    (c1 c2 : Capability_GS.t)
    (alloc1 alloc2 : allocation)
    (* allocations must be sane *)
    (AL1: AddressValue.to_Z (base alloc1) + Z.of_nat (size alloc1) <= AddressValue.ADDR_LIMIT)
    (AL2: AddressValue.to_Z (base alloc2) + Z.of_nat (size alloc2) <= AddressValue.ADDR_LIMIT)
    (SZ: 0 <= sz):

    memcpy_alloc_bounds_check_p c1 c2 alloc1 alloc2 sz ->

    (* upper limit is within bounds. NB [<= AddressValue.ADDR_LIMIT] *)
    (AddressValue.ADDR_MIN <=
       AddressValue.to_Z (Capability_GS.cap_get_value c1) + sz <=
       AddressValue.ADDR_LIMIT) /\
      (AddressValue.ADDR_MIN <=
         AddressValue.to_Z (Capability_GS.cap_get_value c2) + sz <=
         AddressValue.ADDR_LIMIT) /\

      (* all addresses are within bounds *)
      (forall x, 0<=x<sz  ->
                 ((AddressValue.ADDR_MIN <=
                     AddressValue.to_Z (Capability_GS.cap_get_value c1) + x <
                     AddressValue.ADDR_LIMIT)
                  /\
                    (AddressValue.ADDR_MIN <=
                       AddressValue.to_Z (Capability_GS.cap_get_value c2) + x <
                       AddressValue.ADDR_LIMIT))).
  Proof.
    intros [H2 [H3 [H4 [H5 H6]]]].

    unfold cap_to_Z in *.
    generalize dependent (Capability_GS.cap_get_value c1); intros a1.
    generalize dependent (Capability_GS.cap_get_value c2); intros a2.
    generalize dependent (base alloc1); intros b1.
    generalize dependent (base alloc2); intros b2.
    generalize dependent (size alloc1); intros s1.
    generalize dependent (size alloc2); intros s2.
    clear alloc1 alloc2.
    intros AL2 AL1 H4 H5 H2 H3 H6.
    pose proof (AddressValue.to_Z_in_bounds a1).
    pose proof (AddressValue.to_Z_in_bounds a2).
    pose proof (AddressValue.to_Z_in_bounds b1).
    pose proof (AddressValue.to_Z_in_bounds b2).

    unfold AddressValue.ADDR_MIN, AddressValue.ADDR_LIMIT in *.

    repeat split; intros; lia.
  Qed.

  Lemma store_unspecified_uchar_spec
    {loc: location_ocaml}
    {c: Capability_GS.t}
    {s s0: mem_state}
    {fp: footprint}
    :
    store loc CoqCtype.unsigned_char false
      (PVconcrete c)
      (MVunspecified CoqCtype.unsigned_char) s = (s0, inr fp)
    ->
      AMap.M.MapsTo (Capability_GS.cap_get_value c) None (bytemap s0).
  Proof.
    intros H.
    unfold store in H.
    state_inv_step.

    rewrite MorelloImpl.uchar_size in H6, H11.
    cbn in H6. apply ret_inr in H6. invc H6.
    cbn in H11. apply ret_inr in H11. invc H11.
    cbn.
    rewrite AddressValue_as_ExtOT.with_offset_0.
    apply AMap.M.add_1.
    reflexivity.
  Qed.

  Lemma bytemap_copy_data_spec
    {a1 a2 : AddressValue.t}
    {n : nat}
    {bm: AMap.M.t (option ascii)}
    :
    AddressValue.to_Z a1 + Z.of_nat n <= AddressValue.ADDR_LIMIT ->
    forall (addr:  AddressValue.t),
      AMap.M.find (elt:=(option ascii)) addr (bytemap_copy_data a1 a2 n bm) =
        AMap.M.find (elt:=(option ascii))
          (if (0 <=? (addr_offset addr a1)) && ((addr_offset addr a1) <? (Z.of_nat n))
           then (AddressValue.with_offset a2 (addr_offset addr a1))
           else addr) bm.
  Proof.
    intros L addr.
    induction n.
    -
      cbn.
      break_match_goal.
      +
        bool_to_prop_hyp.
        lia.
      +
        reflexivity.
    -
      cbn.
      destruct (Z.eq_dec (addr_offset addr a1) (Z.of_nat n)) as [E|NE].
      +
        repeat break_if;bool_to_prop_hyp;try lia.
        rewrite E in *.
        clear H H1 H0.
        assert(addr = AddressValue.with_offset a1 (Z.of_nat n)).
        {
          assert(0<=addr_offset addr a1) by lia.
          rewrite <- E.
          clear -H.
          symmetry.
          apply with_offset_addr_offset.
        }
        rewrite <- H.

        break_match_goal.
        *
          rewrite AMap.F.add_eq_o by reflexivity.
          reflexivity.
        *
          rewrite AMap.F.remove_eq_o by reflexivity.
          reflexivity.
      +
        replace (addr_offset addr a1 <? Z.of_nat (S n)) with
          (addr_offset addr a1 <? Z.of_nat n).
        2:{
          clear -NE.
          apply ltb_equiv_propositional.
          lia.
        }
        rewrite <- IHn. clear IHn.
        *
          assert(OE: AddressValue.with_offset a1 (Z.of_nat n) <> addr).
          {
            clear - L NE.
            contradict NE.
            rewrite <- NE. clear NE.
            apply addr_offset_with_offset.
            pose proof (AddressValue.to_Z_in_bounds a1).
            unfold AddressValue.ADDR_MIN in *.
            lia.
          }
          break_match_goal.
          --
            apply AMap.F.add_neq_o, OE.
          --
            rewrite AMap.F.remove_neq_o; [reflexivity|apply OE].
        *
          lia.
  Qed.

  Lemma memcpy_copy_data_spec
    {loc : location_ocaml}
    {s s' : mem_state_r}
    {a1 a2 : AddressValue.t}
    {n : nat}
    (C: memcpy_copy_data loc a1 a2 n s = (s', inr tt))
    (L: AddressValue.to_Z a1 + Z.of_nat n <= AddressValue.ADDR_LIMIT)
    :

    forall (addr:  AddressValue.t),
      AMap.M.find (elt:=(option ascii)) addr (bytemap s') =
        AMap.M.find (elt:=(option ascii))
          (if (0 <=? (addr_offset addr a1)) && ((addr_offset addr a1) <? (Z.of_nat n))
           then (AddressValue.with_offset a2 (addr_offset addr a1))
           else addr)
          (bytemap s).
  Proof.
    intros addr.
    unfold memcpy_copy_data in C.
    apply update_mem_state_spec in C.
    subst.
    apply (bytemap_copy_data_spec L).
  Qed.


  Lemma capmeta_ghost_tags_preserves:
    forall m addr size,
      mem_invariant m ->
      mem_invariant (mem_state_with_capmeta
                       (capmeta_ghost_tags addr size (capmeta m))
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
      (* alignment proof *)
      intros a E.
      apply AMapProofs.map_in_mapsto in E.
      destruct E as [tg E].
      unfold mem_state_with_capmeta in E.
      simpl in E.
      destruct tg as (tg,gs).
      apply capmeta_ghost_tags_monotone in E.
      +
        destruct E as [tg' [gs' [E1 _]]].
        apply AMapProofs.map_mapsto_in in E1.
        apply Balign.
        apply E1.
    -
      intros a g E U bs F.
      simpl in *.
      apply capmeta_ghost_tags_monotone in E.
      destruct E as [tg' [gs' [E1 [[E2g E2u]|[E3g [E3u [E4u E5u]]]] ]]]; subst.
      *
        eapply MIcap; eauto.
      *
        eapply MIcap; eauto.
  Qed.


  Fact store_lock_preserves
    (s0 : storage_instance_id)
    (s : mem_state_r):
    mem_invariant s ->
    mem_invariant
      (mem_state_with_allocations
         (ZMap.map_update s0
            (fun oa : option allocation =>
               a <- oa;;
               ret
                 (allocation_with_is_readonly a
                    (IsReadOnly
                       match prefix a with
                       | PrefStringLiteral _ _ => MemCommonExe.ReadonlyStringLiteral
                       | PrefTemporaryLifetime _ _ => MemCommonExe.ReadonlyTemporaryLifetime
                       | _ => MemCommonExe.ReadonlyConstQualified
                       end))) (allocations s)) s).
  Proof.
    intros H.

    destruct H as [MIbase MIcap].
    destruct_base_mem_invariant MIbase.
    unfold mem_state_with_allocations.

    Transparent ret bind.
    unfold Monad_option, ret, bind.
    Opaque ret bind.
    unfold allocation_with_is_readonly.
    cbn.

    split.
    -
      (* base *)
      clear MIcap.
      repeat split;cbn.
      1,3,6:
        apply ZMapProofs.map_forall_update;[assumption|];
      unfold ZMapProofs.option_pred;
      intros oa;
      destruct oa;auto.
      2:auto.
      +
        (* Bnooverlap *)
        intros alloc_id1 alloc_id2 a1 a2 H H0 H1.
        destruct (ZMap.M.E.eq_dec alloc_id1 s0) as [E1|NE1], (ZMap.M.E.eq_dec alloc_id2 s0) as [E2|NE2].
        *
          congruence.
        *
          subst s0.
          apply ZMapProofs.map_update_MapsTo_not_at_k in H1;auto.
          apply ZMapProofs.map_update_at_k_cases in H0.
          destruct H0 as [[a [M IN]]|[OUT M]];[|inversion M].
          invc IN.
          specialize (Bnooverlap _ _ _ _ H M H1).
          clear - Bnooverlap.
          destruct a2,a.
          unfold allocations_do_no_overlap in *.
          cbn in *.
          lia.
        *
          subst s0.
          apply ZMapProofs.map_update_MapsTo_not_at_k in H0;auto.
          apply ZMapProofs.map_update_at_k_cases in H1.
          destruct H1 as [[a [M IN]]|[OUT M]];[|inversion M].
          invc IN.
          specialize (Bnooverlap _ _ _ _ H H0 M).
          clear - Bnooverlap.
          destruct a1,a.
          unfold allocations_do_no_overlap in *.
          cbn in *.
          lia.
        *
          apply ZMapProofs.map_update_MapsTo_not_at_k in H0,H1;auto.
          apply (Bnooverlap _ _ _ _ H H0 H1).
      +
        (* Bnextallocid *)
        intros k M.
        apply ZMapProofs.map_in_mapsto in M.
        destruct M as [v M].
        rename s0 into k'.
        destruct (ZMap.M.E.eq_dec k' k) as [E|NE].
        *
          subst k'.
          destruct (ZMap.F.In_dec (allocations s) k) as [IN|OUT].
          --
            apply ZMapProofs.map_in_mapsto in IN.
            destruct IN as [v' IN].
            pose proof (ZMapProofs.map_update_MapsTo_update_at_k IN M) as U.
            clear M.
            cbn in U.
            invc U.
            apply Bnextallocid.
            apply ZMapProofs.map_mapsto_in in IN.
            assumption.
          --
            pose proof (ZMapProofs.map_update_MapsTo_new_at_k OUT M) as U.
            cbn in U.
            inversion U.
        *
          apply (ZMapProofs.map_update_MapsTo_not_at_k (allocations s)) in M;auto.
          apply Bnextallocid.
          apply ZMapProofs.map_mapsto_in in M.
          assumption.
    -
      (* main invariant *)
      intros addr g M U bs F.
      cbn in *.
      specialize (MIcap addr g M U bs F).
      destruct MIcap as [c [D [a [alloc_id [M1 B]]]]].
      exists c.
      split;[assumption|].

      destruct (ZMap.M.E.eq_dec alloc_id s0) as [E|NE].
      +
        subst s0.
        exists {|
            prefix := prefix a;
            base := base a;
            size := size a;
            ty := ty a;
            is_readonly :=
              IsReadOnly
                match prefix a with
                | PrefStringLiteral _ _ => MemCommonExe.ReadonlyStringLiteral
                | PrefTemporaryLifetime _ _ => MemCommonExe.ReadonlyTemporaryLifetime
                | _ => MemCommonExe.ReadonlyConstQualified
                end;
            is_dynamic := is_dynamic a;
            is_dead := is_dead a
          |}, alloc_id.
        split;[|assumption].
        eapply ZMapProofs.map_update_MapsTo_update_at_k';eauto.
      +
        exists a, alloc_id.
        split;auto.
        apply ZMapProofs.map_update_MapsTo_not_at_k;auto.
  Qed.


  (* TODO move to Proof Aux *)
  Fact option2serr_inv {A:Type}:
    forall msg (o:option A) v,
    option2serr msg o = inr v -> o = Some v.
  Proof.
    intros msg o v H.
    destruct o.
    -
      cbn in H.
      apply ret_inr in H.
      inv H.
      reflexivity.
    -
      cbn in H.
      apply raise_serr_inr_inv in H.
      tauto.
  Qed.
    
  Fact pointer_sizeof_pos:
    (0 < sizeof_pointer MorelloImpl.get)%nat.
  Proof.
    rewrite pointer_sizeof_alignof.
    apply MorelloImpl.alignof_pointer_pos.
  Qed.

  Lemma sizeof_pos:
    forall fuel szn maybe_tagDefs ty,
      sizeof fuel maybe_tagDefs ty = inr szn -> (0 < szn)%nat

  with
  offsetof_struct_max_offset_pos:
    forall fuel t s l max_offset,
      offsetsof_struct fuel t s = inr (l, max_offset) -> (0 < max_offset)%nat.
  Proof.
    -
      clear sizeof_pos.
      induction fuel as [| fuel' IHfuel] using nat_ind.
      + (* Base case: fuel = 0 *)
        intros szn maybe_tagDefs ty H.
        simpl in H.
        discriminate.
      +
        intros szn maybe_tagDefs ty H.
        simpl in H.

        destruct ty as [a cty].
        destruct cty eqn:TY.
        all: try inversion H.
        *
          destruct b.
          --
            apply option2serr_inv in H1.
            apply MorelloImpl.sizeof_ity_pos in H1. assumption.
          --
            apply option2serr_inv in H1.
            apply MorelloImpl.sizeof_fty_pos in H1. assumption.
        *
          destruct o.
          --
            state_inv_step;
              apply IHfuel in H2;
              lia.
          --
            state_inv_step.
        *
          pose proof pointer_sizeof_pos as P.
          remember (sizeof_pointer MorelloImpl.get) as psize.
          break_match_goal.
          --
            invc Heqs.
          --
            apply ret_inr in Heqs.
            invc Heqs.
            assumption.
        *
          apply IHfuel in H1.
          assumption.
        *
          (* struct *)
          generalize dependent (match maybe_tagDefs with
                                | Some x => x
                                | None => AbstTagDefs.tagDefs tt
                                end); intros.

          clear H1.

          apply bind_serr_inv in H.
          destruct H as [x [H1 H2]].
          break_let.
          clear Heqp x.
          rename n into max_offset.
          eapply offsetof_struct_max_offset_pos in H1.
          state_inv_step;bool_to_prop_hyp; try congruence;lia.
        *
          (* Union *)
          generalize dependent (match maybe_tagDefs with
                                | Some x => x
                                | None => AbstTagDefs.tagDefs tt
                                end); intros.

          clear H1.
          break_match_hyp;[|inv H].
          break_match_hyp;[inv H|].
          state_inv_step;
            bool_to_prop_hyp.
          --
            rename szn into max_size, n0 into max_align.
            clear - Heqn1 Heqb H2 IHfuel.

            remember (S n1) as n.
            assert(n <> O) as N by lia.
            clear Heqn n1.
            cut (max_size <> O);[lia|].

            (* TODO: proof by induction on [l] *)
            admit.
          --
            rename n into max_size, n0 into max_align.
            clear - Heqn1 Heqb H2 IHfuel.

            remember (S n1) as n.
            assert(n <> O) as N by lia.
            clear Heqn n1.

            cut (max_size <> O);[lia|].

            (* TODO: same as previous bullet *)
            admit.
    -
      clear offsetof_struct_max_offset_pos.
      intros fuel t s l max_offset OF.
      induction fuel; intros.
      +
        simpl in OF.
        discriminate OF.
      +
        cbn in OF.

        break_match_hyp;[|discriminate OF].
        break_match_hyp.
        *
          (* struct *)
          apply bind_sassert_inv in OF.
          destruct OF as [L OF].
          destruct (Datatypes.length l0) eqn:L0.
          inv L.
          clear L.

          apply bind_serr_inv in OF.
          destruct OF as [x [H1 H2]].
          break_let.
          inl_inr_inv.
          subst.

          remember (match o with
                    | Some (CoqCtype.FlexibleArrayMember attrs ident qs ty) => l0 ++ [(ident, (attrs, None, qs, ty))]
                    | None => l0
                    end) as l0'.

          assert(0 < length l0')%nat.
          {
            destruct o.
            -
              destruct f.
              subst l0'.
              pose proof (app_length l0 [(i, (a, None, q, c))]).
              rewrite H.
              lia.
            -
              subst.
              lia.
          }
          clear Heql0' l0 L0 Heqo.
          rename l0' into l0.

          revert H.
          induction l0;intros.
          --
            setoid_rewrite list.nil_length in H.
            lia.
          --
            cbn in H1.

            apply bind_serr_inv in H1.
            destruct H1 as [a' [H2 H3]].
            repeat break_let.

            destruct a'.
            rename n0 into max_offset'.

            apply bind_serr_inv in H2.
            destruct H2 as [size [H2 H4]].

            apply bind_serr_inv in H4.
            destruct H4 as [align [H4 H5]].
            inl_inr_inv.

            assert(0<max_offset')%nat.
            {
              cut (0<size)%nat.
              intros H0.
              lia.
              clear - sizeof_pos H2.
              eapply sizeof_pos.
              eauto.
            }
  Admitted.

  Lemma repr_preserves
    (fuel : nat)
    (mval: mem_value)
    (c : Capability_GS.t)
    (s : mem_state_r)
    (M: mem_invariant s)
    (bs : list (option ascii))
    (funptrmap0 : ZMap.M.t (digest * string * Capability_GS.t))
    (capmeta0 : AMap.M.t (bool * CapGhostState)):

    repr fuel (CheriMemoryImplWithProofs.funptrmap s) (CheriMemoryImplWithProofs.capmeta s)
      (Capability_GS.cap_get_value c) mval = inr (funptrmap0, capmeta0, bs)

    ->
    mem_invariant
      (mem_state_with_funptrmap_bytemap_capmeta funptrmap0
         (AMap.map_add_list_at (bytemap s) bs (Capability_GS.cap_get_value c)) capmeta0 s).
  Proof.
    intros R.

    unfold repr in R.
    destruct fuel;[apply raise_either_inr_inv in R;tauto|].

    destruct M as [MIbase MIcap].
    destruct_base_mem_invariant MIbase.
    (* base *)
    break_match_hyp.
    - (* MVunspecified *)
      (* [state_inv_step] should work here. TODO: investigate why it stucks *)
      apply bind_serr_inv in R.
      destruct R as [szn [R1 R2]].
      rewrite ret_serr_inv in R2.
      invc R2.

      (*
        generalize dependent DEFAULT_FUEL; intros sfuel R2.
        unfold sizeof in R2.
        destruct sfuel;[apply raise_either_inr_inv in R2;tauto|].
       *)

      assert(0 < szn)%nat as SP.
      {
        apply sizeof_pos in R1.
        apply R1.
      }

      generalize (Capability_GS.cap_get_value c) as start.
      intros start.
      clear c.

      unfold mem_state_with_funptrmap_bytemap_capmeta.
      repeat split;cbn;auto.
      +
        (* Balign *)
        pose proof (capmeta_ghost_tags_preserves s start szn) as P.
        autospecialize P.
        repeat split;auto.
        apply P.
      +
        (* MIcap *)
        intros addr g M U bs F.
        remember (alignof_pointer MorelloImpl.get) as palignment.
        remember(align_down (AddressValue.to_Z start) (Z.of_nat palignment)) as a0.
        remember(align_down (AddressValue.to_Z start + (Z.of_nat szn - 1)) (Z.of_nat palignment)) as a1.

        assert(decidable (a0 <= AddressValue.to_Z addr <= a1)) as AR
            by (apply dec_and; apply Z.le_decidable).

        destruct AR as [IN|OUT].
        *
          (* a0 <= AddressValue.to_Z addr <= a1 *)
          subst.
          pose proof (capmeta_ghost_tags_spec_in_range_aligned start szn SP
                        (capmeta s)
                        addr
                        IN
                        true
                        g
                        M
            )
            as CA.
          destruct CA;congruence.
        *
          (* ~ a0 <= AddressValue.to_Z addr <= a1 *)
          subst.
          pose proof (capmeta_ghost_tags_spec_outside_range_aligned start szn SP
                        (capmeta s)
                        addr
                        OUT
                        true
                        g
                        M
            )
            as CA.

          remember (fetch_bytes (AMap.map_add_list_at (bytemap s) (repeat None szn) start) addr
                      (sizeof_pointer MorelloImpl.get)) as bs.
          specialize (MIcap addr g CA U bs).
          apply MIcap.

          (* prove bytes unchanged *)
          subst bs.
          clear - OUT.

          (* prep *)
          remember (sizeof_pointer MorelloImpl.get) as psize.
          remember (alignof_pointer MorelloImpl.get) as palign.

          remember (list_init psize (fun i0 : nat => AddressValue.with_offset addr (Z.of_nat i0))) as rl.
          assert(length rl = psize).
          {
            subst rl.
            apply list_init_len.
          }


          (* meat *)
          unfold fetch_bytes.
          apply map_ext_in.

          intros a IN.
          apply In_nth_error in IN.
          destruct IN as [off IN].
          assert(off < psize)%nat.
          {
            cut(nth_error (list_init psize (fun i : nat => AddressValue.with_offset addr (Z.of_nat i))) off <> None).
            intros H0.
            apply nth_error_Some in H0.
            rewrite list_init_len in H0.
            auto.
            rewrite IN.
            discriminate.
          }
          rewrite list_init_nth in IN;[|auto].
          invc IN.
          clear H.

          (* TODO: need [AMap.map_add_list_at] spec *)

          admit.
    -

  Admitted.

  Instance store_PreservesInvariant
    (loc : location_ocaml)
    (cty : CoqCtype.ctype)
    (is_locking : bool)
    (ptr : pointer_value)
    (mval : mem_value):
    forall s, PreservesInvariant mem_invariant s (store loc cty is_locking ptr mval).
  Proof.
    intros s.
    unfold store.
    preserves_step.
    preserves_step.
    break_if;[preserves_step|].
    break_match_goal;[preserves_step|].
    preserves_step.
    apply SameStatePreserves, find_cap_allocation_SameState.
    break_match_goal;[|preserves_step].
    break_let.
    break_if;[preserves_step|].
    preserves_step.
    apply SameStatePreserves, is_within_bound_SameState.
    break_if;[|preserves_step].
    preserves_step.
    apply SameStatePreserves, get_allocation_SameState.
    break_match_goal;[|preserves_step].
    preserves_step.
    apply SameStatePreserves, is_atomic_member_access_SameState.
    break_if;[preserves_step|].
    preserves_step.
    -
      preserves_step;[preserves_step|].
      preserves_step;[apply SameStatePreserves, cap_check_SameState|].
      preserves_step.
      apply bind_PreservesInvariant_value_SameState.
      typeclasses eauto.
      intros H x6 H0.
      repeat break_let.
      preserves_step;[|preserves_step].
      preserves_step.
      apply serr2InternalErr_inv in H0.
      destruct x5.
      subst.
      clear - s'5 H H0.
      rename
        s'5 into s,
        H into M,
        H0 into R,
        t1 into capmeta,
        t0 into funptrmap,
        l into bs.
      eapply repr_preserves;eauto.
    -
      (* handling `is_locking` *)
      break_if;[|preserves_step].
      preserves_steps.
      apply store_lock_preserves, H.
  Qed.

  Lemma memcpy_copy_data_fetch_bytes_spec
    {loc:location_ocaml}
    {s s': mem_state_r}
    {ptrval1 ptrval2: pointer_value}
    {len: Z}
    :
    base_mem_invariant s ->
    mempcpy_args_sane s.(allocations) ptrval1 ptrval2 len ->
    forall c1 c2 a1 a2,
      ptrval1 = PVconcrete c1 ->
      ptrval2 = PVconcrete c2 ->
      a1 = Capability_GS.cap_get_value c1 ->
      a2 = Capability_GS.cap_get_value c2 ->
      memcpy_copy_data loc a1 a2 (Z.to_nat len) s = (s', inr tt) ->
      fetch_bytes (bytemap s') a1 (Z.to_nat len) = fetch_bytes (bytemap s') a2 (Z.to_nat len).
  Proof.
    intros Mbase H0 c1 c2 a1 a2 H1 H2 H3 H4 H5.
    unfold fetch_bytes.
    apply list.list_eq_Forall2.
    eapply Forall2_nth_list.
    -
      rewrite 2!map_length.
      subst.
      rewrite 2!list_init_len.
      reflexivity.
    -
      rewrite map_length, list_init_len.
      intros i H.
      rewrite 2!map_nth with (d:=(AddressValue.of_Z AddressValue.ADDR_MIN)).

      pose proof (list_init_nth _ (fun i : nat => AddressValue.with_offset a1 (Z.of_nat i)) _ H) as LI1.
      eapply nth_error_nth in LI1.
      rewrite LI1.
      clear LI1.

      pose proof (list_init_nth _ (fun i : nat => AddressValue.with_offset a2 (Z.of_nat i)) _ H) as LI2.
      eapply nth_error_nth in LI2.
      erewrite LI2.
      clear LI2.

      remember (Z.to_nat len) as n eqn:N.
      replace len with (Z.of_nat n) in H0 by lia.
      clear len N.

      (* mem copy with dst= s'[a1+i] *)
      assert(AddressValue.to_Z a1 + Z.of_nat n <= AddressValue.ADDR_LIMIT) as L.
      {
        clear H5.
        invc H0.
        invc H14.
        invc H15.
        invc H10.
        invc H11.
        invc H12.

        (* We only need Bfit from Mbase *)
        destruct_base_mem_invariant Mbase.
        clear Bdead Bnooverlap Balign Bnextallocid Blastaddr.

        unfold cap_to_Z in *.
        specialize (Bfit alloc_id1 alloc1 H6).
        cbn in Bfit.

        clear  - Bfit H4 H10.
        destruct H10 as [H1 [_ [_ _]]].
        lia.
      }
      pose proof (memcpy_copy_data_spec H5 L (AddressValue.with_offset a1 (Z.of_nat i)))
        as M1.

      (* goal s'[a2+i] = s'[a1+i]. English: source and destination regions equal in s' *)
      break_match_hyp.
      +
        (* destination `a1+i` within bounds [a1,a1+n) *)
        rewrite M1; clear M1.

        replace (AddressValue.with_offset a2 (addr_offset (AddressValue.with_offset a1 (Z.of_nat i)) a1))
          with (AddressValue.with_offset a2 (Z.of_nat i)).
        2:{
          bool_to_prop_hyp.
          rewrite addr_offset_with_offset.
          reflexivity.

          (* We only need Bfit from Mbase *)
          destruct_base_mem_invariant Mbase.
          clear Bdead Bnooverlap Balign Bnextallocid Blastaddr.

          invc H0.
          invc H17.
          invc H18.

          pose proof (memcpy_alloc_bounds_check_p_c_bounds (Z.of_nat n) c1 c2 alloc1 alloc2) as [BL1 [BL2 B]].
          apply (Bfit alloc_id1 alloc1 H9).
          apply (Bfit alloc_id2 alloc2 H10).
          lia.
          assumption.
          specialize (B (Z.of_nat i)).
          autospecialize B;[lia|].
          lia.
        }

        (* goal s[a2+i] = s'[a2+i]. English: source region unchanged *)

        (* mem copy with dst= s'[a2+i] *)
        pose proof (memcpy_copy_data_spec H5 L (AddressValue.with_offset a2 (Z.of_nat i))) as M2.
        break_match_hyp.
        *
          (* destination `a2+i` is in bounds [a1,a1+n). This is is an overlap! *)
          exfalso.
          (* We only need Bfit from Mbase *)
          destruct_base_mem_invariant Mbase.
          clear Bdead Bnooverlap Balign Bnextallocid Blastaddr.
          invc H0.
          invc H15.
          invc H16.
          pose proof (memcpy_alloc_bounds_check_p_c_bounds (Z.of_nat n)  c1 c2 alloc1 alloc2) as [BL1 [BL2 B]].
          apply (Bfit alloc_id1 alloc1 H7).
          apply (Bfit alloc_id2 alloc2 H8).
          lia.
          assumption.
          specialize (B (Z.of_nat i)).
          autospecialize B;[lia|].
          bool_to_prop_hyp.
          invc H13.
          (* destruct H4 as [_ [_ [_ H11]]]. *)
          unfold cap_to_Z in *.
          destruct B.
          rewrite addr_offset_with_offset in * by lia.
          unfold addr_offset in *.
          rewrite AddressValue.with_offset_no_wrap in * by lia.
          pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c1)).
          pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c2)).
          unfold AddressValue.ADDR_MIN in *.
          lia.
        (* phew! *)
        *
          rewrite M2;
            reflexivity.
      +
        (* We only need Bfit from Mbase *)
        destruct_base_mem_invariant Mbase.
        clear Bdead Bnooverlap Balign Bnextallocid Blastaddr.
        invc H0.
        invc H15.
        invc H16.

        pose proof (memcpy_alloc_bounds_check_p_c_bounds (Z.of_nat n)  c1 c2 alloc1 alloc2) as [BL1 [BL2 B]].
        apply (Bfit alloc_id1 alloc1 H7).
        apply (Bfit alloc_id2 alloc2 H8).
        lia.
        assumption.
        specialize (B (Z.of_nat i)).
        autospecialize B;[lia|].

        invc H13.
        unfold cap_to_Z in *.
        destruct B.
        rewrite addr_offset_with_offset in * by lia.
        unfold addr_offset in *.
        pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c1)).
        pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c2)).
        unfold AddressValue.ADDR_MIN in *.

        lia.
  Qed.

  Lemma memcpy_arg_sane_after_check
    (ptrval1 ptrval2 : pointer_value)
    (s s' : mem_state_r)
    (loc : location_ocaml)
    (n : Z):
    memcpy_args_check loc ptrval1 ptrval2 n s = (s', inr tt) ->
    mempcpy_args_sane s.(allocations) ptrval1 ptrval2 n.
  Proof.
    intros H.

    pose proof (memcpy_args_check_SameState loc ptrval1 ptrval2 n) as SA.
    specialize (SA _ _ _ H).
    subst s'.

    unfold memcpy_args_check in H.
    Transparent raise ret fail.
    unfold fail, raise, ret, Monad_either, Exception_either, Exception_errS, memM_monad, Monad_errS in H.
    cbn in H.
    repeat break_match; try tuple_inversion; try inl_inr.
    repeat state_inv_step.

    unfold find_cap_allocation in *.
    repeat state_inv_step.
    tuple_inversion.
    apply find_cap_allocation_st_spec in H0, H1.
    destruct H0 as [H0 [D0 B0]].
    destruct H1 as [H1 [D1 B1]].
    apply ZMap.M.find_2 in H0, H1.

    apply orb_false_elim in Heqb0.
    destruct Heqb0.

    unfold memcpy_alloc_bounds_check in H3.
    break_match_hyp. state_inv_step.
    break_match_hyp; state_inv_step.
    bool_to_prop_hyp.

    econstructor.
    - auto.
    - eapply H1.
    - eapply H0.
    - auto.
    - auto.
    - auto.
    - auto.
    -
      unfold cap_bounds_within_alloc in B0,B1.
      destruct B0.
      destruct B1.
      constructor; try split.
      +
        unfold cap_to_Z in *.
        lia.
      +
        unfold cap_to_Z in *.
        lia.
      +
        unfold cap_to_Z in *.
        lia.
  Qed.

  Lemma fetch_bytes_subset
    (a1 a2 a1' a2':AddressValue.t)
    (n n':nat)
    (bm: AMap.M.t (option ascii))
    (A1: forall x, 0<=x<Z.of_nat n -> 0 <= AddressValue.to_Z a1 + x < AddressValue.ADDR_LIMIT)
    (A2: forall x, 0<=x<Z.of_nat n -> 0 <= AddressValue.to_Z a2 + x < AddressValue.ADDR_LIMIT)
    (E: fetch_bytes bm a1 n = fetch_bytes bm a2 n):

    (exists (off:Z),
        off >= 0
        /\ a1' = AddressValue.with_offset a1 off
        /\ a2' = AddressValue.with_offset a2 off
        /\ off <= Z.of_nat n
        /\ (n' + (Z.to_nat off) <= n)%nat)
    ->
      fetch_bytes bm a1' n' = fetch_bytes bm a2' n'.
  Proof.
    assert (length (fetch_bytes bm a1 n) = n) by apply fetch_bytes_len.
    assert (length (fetch_bytes bm a2 n) = n) by apply fetch_bytes_len.
    assert (length (fetch_bytes bm a1' n') = n') by apply fetch_bytes_len.
    assert (length (fetch_bytes bm a2' n') = n') by apply fetch_bytes_len.

    intros [off [E1 [E2 [E3 [E4 E5]]]]].
    apply list.list_eq_Forall2.

    eapply Forall2_nth_list; [lia|].
    intros i I.

    rewrite H1 in I.
    unfold fetch_bytes, list_init.
    rewrite 4!map_nth.
    rewrite 2!seq_nth; try lia.
    rewrite plus_O_n.

    apply list.list_eq_Forall2 in E.
    eapply Forall2_nth_list' with (i:=Z.to_nat (off+(Z.of_nat i))) in E.
    2:{
      rewrite H.
      lia.
    }


    unfold fetch_bytes, list_init in E.
    rewrite 4!map_nth in E.
    rewrite 2!seq_nth in E; try lia.
    rewrite plus_O_n in E.


    rewrite Z2Nat.id in E by lia.


    assert(0 <= off ) by lia.
    assert(0 <= Z.of_nat i) by lia.

    assert(0 <= AddressValue.to_Z a1 + (off + Z.of_nat i) < AddressValue.ADDR_LIMIT).
    {
      clear - A1 E1 E4 E5 I.
      pose proof (AddressValue.to_Z_in_bounds a1) as [B0 B1].
      remember (AddressValue.to_Z a1) as az1.
      clear Heqaz1.
      zify.
      unfold AddressValue.ADDR_MIN in *.
      specialize (A1 (off + Z.of_nat i)).
      lia.
    }

    assert(0 <= AddressValue.to_Z a2 + (off + Z.of_nat i) < AddressValue.ADDR_LIMIT).
    {
      clear - A2 E1 E4 E5 I.
      pose proof (AddressValue.to_Z_in_bounds a2) as [B0 B1].
      remember (AddressValue.to_Z a2) as az2.
      clear Heqaz2.
      zify.
      unfold AddressValue.ADDR_MIN in *.
      specialize (A2 (off + Z.of_nat i)).
      lia.
    }

    subst a1' a2'.
    setoid_rewrite <- with_pos_offset_assoc in E; auto.

    Unshelve. exact O.
    Unshelve. exact O.
    Unshelve. exact O.
    Unshelve. exact O.
  Qed.

  Lemma memcpy_copy_data_preserves_allocations:
    forall (loc : location_ocaml) (dst_a src_a : AddressValue.t) (s : mem_state_r)
           (size : nat) (s' : mem_state),
      memcpy_copy_data loc dst_a src_a size s = (s', inr tt)
      ->
        allocations s = allocations s'.
  Proof.
    intros loc dst_a src_a s size s' M.
    unfold memcpy_copy_data in M.
    apply update_mem_state_spec in M.
    unfold mem_state_with_bytemap in M.
    destruct s'.
    cbn.
    invc M.
    reflexivity.
  Qed.

  Fact already_aligned
    (addr: AddressValue.t):
    addr_ptr_aligned addr ->
    AddressValue.of_Z (align_down (AddressValue.to_Z addr) (Z.of_nat (alignof_pointer MorelloImpl.get))) = addr.
  Proof.
    intros A.
    unfold addr_ptr_aligned in A.
    unfold align_down.
    rewrite A.
    rewrite Z.sub_0_r.
    apply AddressValue_of_Z_to_Z.
  Qed.

  Fact align_down_le:
    forall v a,
      0<a ->
      align_down v a <= v.
  Proof.
    intros v a H0.
    unfold align_down.
    apply Z.le_sub_nonneg.
    apply numbers.Z.mod_pos.
    apply H0.
  Qed.

  Fact bytemap_mem_state_with_bytemap:
    forall s bm, (bytemap (mem_state_with_bytemap bm s)) = bm.
  Proof.
    intros s bm.
    reflexivity.
  Qed.

  Instance memcpy_copy_data_PreservesInvariant
    (loc: location_ocaml)
    (dst_a src_a: AddressValue.t)
    (n: nat)
    :
    forall s,

      (* In *)
      (forall a : AddressValue.t,
          let alignment := Z.of_nat (alignof_pointer MorelloImpl.get) in
          let a0 := align_down (AddressValue.to_Z dst_a) alignment in
          let a1 := align_up (AddressValue.to_Z dst_a + ((Z.of_nat n) - 1)) alignment in
          (a0 <= AddressValue.to_Z a <= a1) ->
          forall (tg : bool) (gs : CapGhostState),
            AMap.M.MapsTo a (tg, gs) (capmeta s) ->
            tg = false \/ tag_unspecified gs = true) ->

      PreservesInvariant mem_invariant s (memcpy_copy_data loc dst_a src_a n).
  Proof.
    unfold memcpy_copy_data.
    induction n.
    +
      intros s _.
      preserves_step.
      cbn.
      unfold mem_state_with_bytemap.
      destruct s.
      auto.
    +
      intros s CIN.
      preserves_steps.
      rename H into M.
      *
        (* adding *)
        split.
        --
          (* base *)
          apply M.
        --
          remember (mem_state_with_bytemap
                      (AMap.M.add (AddressValue.with_offset dst_a (Z.of_nat n)) o
                         (bytemap_copy_data dst_a src_a n (bytemap s))) s) as s'.
          assert(capmeta s' = capmeta s).
          {
            destruct s', s.
            invc Heqs'.
            reflexivity.
          }

          intros addr g H0 H1 bs H2.

          (* We expand the lower bound to the previous aligned address.
             The upper bound stays unaligned: [dst_a + (S n) -1] *)
          assert(decidable
                   (
                     (align_down (AddressValue.to_Z dst_a) (Z.of_nat (alignof_pointer MorelloImpl.get)))
                     <= (AddressValue.to_Z addr)
                     <=
                       align_up (AddressValue.to_Z dst_a + (Z.of_nat (S n) - 1)) (Z.of_nat (alignof_pointer MorelloImpl.get))
                ))
            as AR
              by
              (apply dec_and; apply Z.le_decidable).

          assert(AA: addr_ptr_aligned addr).
          {
            destruct M as [MIbase MIcap].
            destruct_base_mem_invariant MIbase.
            (* only need Balign *)
            clear Bfit Bnextallocid Bnooverlap Blastaddr Bdead.
            rewrite H in *.
            specialize (Balign addr).
            autospecialize Balign.
            apply (AMapProofs.map_mapsto_in _ _ _ H0).
            auto.
          }

          destruct AR as [R|NR].
          ++
            (* in range *)
            exfalso.
            (* Caps in range are untagged. H0/H1 is false *)
            clear IHn Heqo H2 bs.

            specialize (CIN addr R true g).
            autospecialize CIN.
            {
              rewrite <- H; auto.
            }
            destruct CIN;congruence.
          ++
            (* outside range *)
            specialize (IHn s).

            (*
            TODO: case anlysis on n/Sn

            autospecialize IHn.
            {
              intros ca CR ctg cgs CM.
              apply (CIN ca);[|auto].
              split;[lia|].

              replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in * by lia.
              assert(CAA: addr_ptr_aligned ca). admit.
              unfold addr_ptr_aligned in CAA.
              unfold align_down in *.
              clear - CR CAA.
              destruct CR.
              nope!
            }
            specialize (IHn M).
            invc IHn.
            rename H3 into MIbase, H4 into MIcap.
            clear CIN.

            eapply MIcap;eauto. clear MIcap.

            remember (bytemap_copy_data ptrval1 ptrval2 n (bytemap s)) as bm.
            remember (AMap.M.add (AddressValue.with_offset ptrval1 (Z.of_nat n)) o bm) as bm'.

            apply not_and in NR;[|apply Z.le_decidable].
            rewrite Z.nle_gt, <- Z.le_ngt, <- Z.ge_le_iff in NR.
            rewrite 2!bytemap_mem_state_with_bytemap.
            clear Heqo.

            (*
              [bm] and [bm'] differ at [ptrval1+n].

              We reading [alignment_size] at [addr].
             *)
            destruct NR as [Nl|Nu].
            **
              rewrite already_aligned in Nl by auto.
              (* addr < ptrval1 ,
                 addr is aligned
               *)
              admit.
            **
              assert(AddressValue.to_Z addr >= AddressValue.to_Z ptrval1 + Z.of_nat (S n)) as Nu'.
              {
                clear - Nu.
                unfold addr_offset in Nu.
                lia.
              }
              (* addr >= prtval+n+1
                 no overlap.
                 the goal could be proven.
               *)
              admit.
             *)
            admit.
      *
        (* removing *)
        admit.
  Admitted. (* TODO: postponed *)


  (* TODO: move *)
  Lemma CapGhostState_eq_dec:
    forall x y : bool * CapGhostState, {x = y} + {x <> y}.
  Proof.
    intros x y.
    decide equality;subst.
    decide equality;subst.
    apply bool_dec.
    apply bool_dec.
    decide equality;subst.
  Qed.

  Lemma capmeta_copy_tags_spec
    (dst src: AddressValue.t)
    (n: nat)
    (step: nat)
    (cm: AMap.M.t (bool * CapGhostState)):
    (0<step)%nat ->
    forall a tg,
      AMap.M.MapsTo a tg (capmeta_copy_tags dst src n step cm) ->
      (* there was a matching tag in src *)
      (exists k,
          0 <= k < Z.of_nat n
          /\ a = AddressValue.with_offset dst (k * Z.of_nat step)
          /\ AMap.M.MapsTo (AddressValue.with_offset src (k * Z.of_nat step)) tg cm)
      \/
        (AMap.M.MapsTo a tg cm
         /\ forall k, 0 <= k < Z.of_nat n -> a <> AddressValue.with_offset dst (k * Z.of_nat step)).
  Proof.
    intros Hstep.
    intros a tg H.
    induction n as [|n' IH]; intros.
    - (* Base case: n = 0 *)
      simpl in H.
      right. split.
      + assumption.
      + intros k Hk. lia.
    - (* Inductive case: n = S n' *)
      cbn in H.
      break_match_hyp.
      +
        (* found, adding *)
        apply AMap.M.find_1 in H.
        rewrite AMap.F.add_o in H.
        break_match_hyp.
        *
          (* a = dst+n*step *)
          invc H.
          rename e into E.
          unfold AddressValue_as_ExtOT.eq in E.
          apply AMap.F.find_mapsto_iff in Heqo.
          subst a.

          destruct (AMapProofs.map_MapsTo_dec (Adec:=CapGhostState_eq_dec) (AddressValue.with_offset src (Z.of_nat n' * Z.of_nat step)) tg cm) as [DE|DNE].
          --
            left.
            exists (Z.of_nat n').
            split. lia.
            split.
            rewrite <- Nat2Z.inj_mul.
            reflexivity.
            apply DE.
          --
            clear IH.
            apply AMap.F.find_mapsto_iff in Heqo.
            contradict DNE.
            apply AMap.F.find_mapsto_iff.
            rewrite <- Heqo.
            rewrite Nat2Z.inj_mul.
            symmetry.
            reflexivity.
        *
          (* a <> dst+n*step *)
          rename n into NE.
          unfold AddressValue_as_ExtOT.eq in NE.
          apply AMap.M.find_2 in H.
          specialize (IH H).
          destruct IH.
          --
            left.
            destruct H0 as [k [H1 [H2 H3]]].
            exists k.
            repeat split; try lia;auto.
          --
            right.
            destruct H0.
            split.
            auto.
            intros k H2.
            unfold AddressValue_as_ExtOT.eq in NE.
            destruct (Z.eq_dec k (Z.of_nat n')) as [KE|KNE].
            ++
              subst k.
              clear - NE.
              rewrite <- Nat2Z.inj_mul.
              auto.
            ++
              apply H1.
              lia.
      +
        (* Not found, removing *)
        apply AMap.M.find_1 in H.
        rewrite AMap.F.remove_o in H.
        break_match_hyp;[inv H|].
        rename n into NE.
        apply AMap.F.find_mapsto_iff  in H.
        specialize (IH H).
        destruct IH.
        *
          left.
          destruct H0 as [k [H1 [H2 H3]]].
          exists k.
          repeat split; try lia;auto.
        *
          right.
          destruct H0.
          split.
          auto.
          intros k H2.
          unfold AddressValue_as_ExtOT.eq in NE.
          destruct (Z.eq_dec k (Z.of_nat n')) as [KE|KNE].
          --
            subst k.
            clear - NE.
            rewrite <- Nat2Z.inj_mul.
            auto.
          --
            apply H1.
            lia.
  Qed.

  Lemma mem_state_after_capmeta_copy_tags_preserves:
    forall m dst src n sz,
      (Z.of_nat n * Z.of_nat (alignof_pointer MorelloImpl.get) = Z.of_nat sz) ->
      addr_ptr_aligned src ->
      addr_ptr_aligned dst ->

      (forall x : Z,
          0 <= x < Z.of_nat sz ->
          AddressValue.ADDR_MIN <= AddressValue.to_Z src + x < AddressValue.ADDR_LIMIT /\
            AddressValue.ADDR_MIN <= AddressValue.to_Z dst + x < AddressValue.ADDR_LIMIT) ->

      (fetch_bytes (bytemap m) src sz = fetch_bytes (bytemap m) dst sz) ->
      mem_invariant m ->
      mem_invariant (mem_state_with_capmeta
                       (capmeta_copy_tags dst src n (alignof_pointer MorelloImpl.get) (capmeta m))
                       m).
  Proof.
    intros m dst src n sz Hsz Hsrc Hdst B DS M.
    remember (alignof_pointer MorelloImpl.get) as step.
    destruct M as [MIbase MIcap].
    destruct_base_mem_invariant MIbase.
    unfold addr_ptr_aligned in *.
    split.
    -
      (* base invariant *)
      clear MIcap.
      repeat split; auto.

      (* alignment proof *)
      intros a E.
      apply AMapProofs.map_in_mapsto in E.
      destruct E as [tg E].
      unfold mem_state_with_capmeta in E.
      simpl in E.
      apply capmeta_copy_tags_spec in E; try lia.
      +
        destruct E as [[k [H1 [H2 H3]]]| [H1 H2]].
        *
          subst a step.
          unfold addr_ptr_aligned.
          rewrite AddressValue.with_offset_no_wrap.
          --
            rewrite Zdiv.Z_mod_plus_full.
            assumption.
          --
            clear - H1 Hsz B.
            unfold AddressValue.ADDR_MIN.
            specialize (B (k * Z.of_nat (alignof_pointer MorelloImpl.get))).
            autospecialize B.
            pose proof MorelloImpl.alignof_pointer_pos.
            nia.
            apply B.
        *
          unfold addr_ptr_aligned.
          subst step.
          apply AMapProofs.map_mapsto_in in H1.
          specialize (Balign a H1).
          auto.
      +
        subst step.
        apply MorelloImpl.alignof_pointer_pos.
    -
      (* the rest of the invariant *)
      intros a g E U bs F.
      simpl in *.
      apply capmeta_copy_tags_spec in E; try lia.
      2:{
        subst step.
        apply MorelloImpl.alignof_pointer_pos.
      }
      destruct E as [E1 | [E2 M]].
      +
        (* in copied meta range *)
        destruct E1 as [k [H1 [H2 H3]]].
        specialize (MIcap (AddressValue.with_offset src (k * Z.of_nat step)) g H3 U bs).
        autospecialize MIcap.
        {
          subst a bs.
          (*
          specialize (B (Z.of_nat sz)).
          autospecialize B. lia.
          unfold AddressValue.ADDR_MIN in B.
          destruct B.
           *)
          apply fetch_bytes_subset with (a1:=src) (a2:=dst) (n:=sz).
          -
            clear - B.
            unfold AddressValue.ADDR_MIN in *.
            apply B.
          -
            clear - B.
            unfold AddressValue.ADDR_MIN in *.
            apply B.
          -
            apply DS.
          -
            exists (k * Z.of_nat step).
            repeat split.
            * nia.
            * nia.
            *
              subst.
              clear - Hdst Hsrc Hsz H1.
              pose proof pointer_sizeof_alignof.
              nia.
        }
        destruct MIcap as [c [M2 [alloc [alloc_id [M3 M4]]]]].
        exists c.
        split;[apply M2|].
        eauto.
      +
        (* outside of copied meta range *)
        specialize (MIcap a g E2 U bs F).
        destruct MIcap as [c [M2 [alloc [alloc_id [M3 M4]]]]].
        exists c.
        split;[apply M2|].
        eauto.
  Qed.

  Fact alignment_correction_correct:
    forall a b : Z, a mod b <> 0 -> 0 < b -> (a + (b - a mod b)) mod b = 0.
  Proof.
    intros a b H H0.
    assert (0 <= a mod b < b) by (apply Z.mod_pos_bound; assumption).
    set (r := a mod b).
    set (d := b - r).
    assert (0 < d <= b) by (unfold d; lia).
    unfold d.
    replace (a + (b - r)) with ((a-r) + b) by lia.
    rewrite mod_add_r by lia.
    unfold r.
    rewrite Zdiv.Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    apply Zdiv.Zmod_0_l.
  Qed.

  Instance memcpy_copy_tags_PreservesInvariant
    (loc : location_ocaml)
    (ptrval1 ptrval2 : pointer_value)
    (s: mem_state)
    (sz : Z)
    (AS: mempcpy_args_sane (allocations s) ptrval1 ptrval2 sz)
    (c1 c2 : Capability_GS.t)
    (a1 a2 : AddressValue.t)
    (P1: ptrval1 = PVconcrete c1)
    (P2: ptrval2 = PVconcrete c2)
    (A1: a1 = Capability_GS.cap_get_value c1)
    (A2: a2 = Capability_GS.cap_get_value c2)
    (F: fetch_bytes (bytemap s) a1 (Z.to_nat sz) = fetch_bytes (bytemap s) a2 (Z.to_nat sz))
    :
    PreservesInvariant mem_invariant s
      (memcpy_copy_tags loc a1 a2 (Z.to_nat sz)).
  Proof.
    inv AS.
    (* it looks, for now like we do not need any allocation stuff from [mempcpy_args_sane].
       we will remove it for now but this may change. *)
    clear H0 H1 H2 H3 H4 H5 H6.
    remember (Capability_GS.cap_get_value c1) as a1 eqn:A1.
    remember (Capability_GS.cap_get_value c2) as a2 eqn:A2.
    invc H8.
    invc H9.
    unfold memcpy_copy_tags.

    (* same alignment check *)
    break_if;bool_to_prop_hyp;[bool_to_prop_hyp|unfold PreservesInvariant;auto].
    rewrite Heqb in *.
    remember (if
                 AddressValue.to_Z (Capability_GS.cap_get_value c2) mod Z.of_nat (alignof_pointer MorelloImpl.get) =? 0
               then 0
               else
                 Z.of_nat (alignof_pointer MorelloImpl.get) -
                   AddressValue.to_Z (Capability_GS.cap_get_value c2) mod Z.of_nat (alignof_pointer MorelloImpl.get))
      as off.
    (* ensure off < zsz *)
    break_if;bool_to_prop_hyp;[unfold PreservesInvariant;auto| bool_to_prop_hyp].
    rewrite Znat.Z2Nat.id in Heqb0 by lia.

    remember (Z.to_nat ((Z.of_nat (Z.to_nat sz) - off) / Z.of_nat (alignof_pointer MorelloImpl.get))) as n.
    preserves_step.

    inversion AS. clear AS. subst allocations0 c0 c3 sz0.
    inversion H0. rename H0 into MM.
    destruct_base_mem_invariant H1.

    pose proof (memcpy_alloc_bounds_check_p_c_bounds sz c1 c2 alloc0 alloc3) as [BL1 [BL2 B]].
    apply (Bfit alloc_id0 alloc0 H4).
    apply (Bfit alloc_id3 alloc3 H5).
    lia.
    apply H11.
    clear H4 H5 H6 H7 H8 H10 H11
      alloc0 alloc3 alloc_id0 alloc_id3
      loc alloc_id1 alloc_id2 alloc1 alloc2.
    clear Bdead Bnooverlap Bfit Balign Bnextallocid Blastaddr.

    apply mem_state_after_capmeta_copy_tags_preserves with (sz:=(n *(alignof_pointer MorelloImpl.get))%nat).
    -
      lia.
    -
      (* [capmeta_copy_tags] [dst] is aligned *)
      subst.
      (* correct relation between `n` and `sz` wrt `alighof_pointer` *)
      break_if; bool_to_prop_hyp.
      +
        rewrite with_offset_0.
        assumption.
      +
        unfold addr_ptr_aligned.
        rewrite AddressValue.with_offset_no_wrap.
        *
          apply alignment_correction_correct.
          -- assumption.
          -- pose proof MorelloImpl.alignof_pointer_pos;lia.
        *
          clear - H Heqb1 Heqb0 B.

          pose proof MorelloImpl.alignof_pointer_pos.
          pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c2)).
          unfold AddressValue.ADDR_MIN in *.

          generalize dependent (AddressValue.to_Z (Capability_GS.cap_get_value c2)).
          generalize dependent (alignof_pointer MorelloImpl.get).
          intros nalign H0 addr Heqb1 Heqb0 B H1.
          remember (Z.of_nat nalign) as align.
          assert(0<align) by lia.
          clear nalign Heqalign H0.
          assert (0 <= addr mod align < align) by (apply Z.mod_pos_bound; assumption).
          split.
          -- lia.
          -- specialize (B (align - addr mod align)); lia.
    -
      subst.
      (* [capmeta_copy_tags] [dst] is aligned *)
      unfold addr_ptr_aligned.
      break_if; bool_to_prop_hyp.
      + rewrite with_offset_0; lia.
      + rewrite <- Heqb.
        rewrite AddressValue.with_offset_no_wrap.
        *
          apply alignment_correction_correct.
          -- rewrite Heqb; assumption.
          -- pose proof MorelloImpl.alignof_pointer_pos;lia.
        *
          apply B.
          clear B.
          split; try lia.
          pose proof MorelloImpl.alignof_pointer_pos.
          pose proof (Z.mod_pos_bound
                        (AddressValue.to_Z (Capability_GS.cap_get_value c1))
                        (Z.of_nat (alignof_pointer MorelloImpl.get))).
          lia.
    -
      intros x H0.
      pose proof MorelloImpl.alignof_pointer_pos.
      break_match_hyp.
      +
        (* c2 is ptr aligned *)
        subst off.
        rewrite 2!with_offset_0.
        rewrite Z.sub_0_r in Heqn.
        apply and_comm, B.
        rewrite Znat.Z2Nat.id in Heqn by lia.
        bool_to_prop_hyp.

        (* clear B BL1 BL2 Heqb0 Heqb1 Heqb c1 c2 H7 s. *)
        split;try lia.
        cut (Z.of_nat (n * alignof_pointer MorelloImpl.get) <= sz).
        lia.
        assert(0 <= Z.of_nat (n * alignof_pointer MorelloImpl.get)) by lia.
        subst n.
        rewrite Nat2Z.inj_mul in *.
        rewrite Z2Nat.id in * by (apply Z.div_pos;lia).
        pose proof (div_mul_undo_le sz (Z.of_nat (alignof_pointer MorelloImpl.get)) H).
        lia.
      +
        (* c2 is not ptr aligned *)
        apply and_comm.
        rewrite Znat.Z2Nat.id in Heqn by lia.
        bool_to_prop_hyp.
        clear BL1 BL2.
        assert(0 < off).
        {
          pose proof (Z.mod_bound_pos (AddressValue.to_Z (Capability_GS.cap_get_value c2)) (Z.of_nat (alignof_pointer MorelloImpl.get))).
          autospecialize H4.
          apply AddressValue.to_Z_in_bounds.
          autospecialize H4.
          lia.
          lia.
        }
        rewrite 2!AddressValue.with_offset_no_wrap.
        2,3:(apply B;lia).
        rewrite <- 2!Z.add_assoc.
        apply B.
        split; [lia|].
        remember (AddressValue.to_Z (Capability_GS.cap_get_value c2)
                    mod Z.of_nat (alignof_pointer MorelloImpl.get)) as rem.
        remember (alignof_pointer MorelloImpl.get) as psize. clear Heqpsize.
        pose proof (AddressValue.to_Z_in_bounds (Capability_GS.cap_get_value c2)).
        remember (AddressValue.to_Z (Capability_GS.cap_get_value c2)) as addr.
        unfold AddressValue.ADDR_MIN in *.
        pose proof (Z.mod_bound_pos addr (Z.of_nat psize)).
        autospecialize H6. lia.
        autospecialize H6. lia.
        subst.
        rewrite Nat2Z.inj_mul in *.
        rewrite Z2Nat.id in * by (apply Z.div_pos;lia).
        zify.
        remember (Z.of_nat psize) as zpsize.
        clear Heqzpsize cstr psize.
        rename zpsize into psize.
        destruct H5, H6, H0.
        remember (AddressValue.to_Z (Capability_GS.cap_get_value c2)) as addr.
        remember (psize - addr mod psize) as off.
        pose proof (div_mul_undo_le (sz-off) psize).
        autospecialize H10. lia.
        autospecialize H10. lia.
        lia.
    -
      symmetry in F.
      apply fetch_bytes_subset
        with
        (a1:=Capability_GS.cap_get_value c2)
        (a2:=Capability_GS.cap_get_value c1)
        (n:=Z.to_nat sz).

      1,2: (rewrite Znat.Z2Nat.id by lia;unfold AddressValue.ADDR_MIN in *;apply B).
      apply F. clear F.
      exists off.

      repeat split; break_match_hyp; bool_to_prop_hyp; try lia.
      +
        subst off.
        pose proof (Zdiv.Z_mod_lt (cap_to_Z c2) (Z.of_nat (alignof_pointer MorelloImpl.get))).
        autospecialize H0.
        pose proof MorelloImpl.alignof_pointer_pos; lia.
        unfold cap_to_Z in H0.
        lia.
      +
        (* off = 0 *)
        subst off n.
        rewrite Znat.Z2Nat.inj_0.
        rewrite Nat.add_0_r.
        rewrite Z.sub_0_r.
        rewrite Znat.Z2Nat.id by lia.
        pose proof MorelloImpl.alignof_pointer_pos.
        rewrite Znat.Z2Nat.inj_div;try lia.
        rewrite Nat.mul_comm.
        rewrite Znat.Nat2Z.id.
        apply Nat.Div0.mul_div_le.
      +
        (* off != 0 *)
        subst off n.
        remember (AddressValue.to_Z (Capability_GS.cap_get_value c1)) as a1; clear Heqa1.
        remember (AddressValue.to_Z (Capability_GS.cap_get_value c2)) as a2; clear Heqa2.
        pose proof MorelloImpl.alignof_pointer_pos.
        remember (alignof_pointer MorelloImpl.get) as ps; clear Heqps.
        remember (Z.of_nat ps - a2 mod Z.of_nat ps) as off.
        assert(0<off).
        {
          subst off.
          pose proof (Z.mod_pos_bound a2 (Z.of_nat ps)).
          lia.
        }
        rewrite Znat.Z2Nat.id in * by assumption.
        rewrite Znat.Z2Nat.inj_div;try lia.
        rewrite Znat.Nat2Z.id.
        assert (0 < Z.of_nat ps) as PSP by lia.
        pose proof (div_mul_undo_le (sz - off) (Z.of_nat ps)) as D.
        autospecialize D. lia.
        specialize (D PSP).
        zify.
        rewrite Nat2Z.inj_div.
        rewrite Znat.Z2Nat.id in * by lia.
        lia.
    -
      assumption.
  Qed.

  Lemma cap_addr_of_pointer_value_inv
    {ptr : pointer_value}
    {a : AddressValue.t}:
    cap_addr_of_pointer_value ptr = inr a ->
    exists c, ptr = PVconcrete c /\ a = Capability_GS.cap_get_value c.
  Proof.
    intros H.
    unfold cap_addr_of_pointer_value in H.
    repeat break_match_hyp.
    inv H.
    apply ret_inr in H.
    exists t.
    split.
    reflexivity.
    inv H.
    reflexivity.
  Qed.

  Lemma ghost_tags_preserves_allocations:
    forall addr size s s',
      ghost_tags addr size s = (s', inr tt)
      ->
        allocations s = allocations s'.
  Proof.
    intros addr size0 s s' H.
    unfold ghost_tags in H.
    apply update_mem_state_spec in H.
    unfold mem_state_with_capmeta in H.
    destruct s'.
    cbn.
    invc H.
    reflexivity.
  Qed.

  Instance ghost_tags_PreservesInvariant
    (addr: AddressValue.t)
    (size: nat)
    :
    forall s, PreservesInvariant mem_invariant s (ghost_tags addr size).
  Proof.
    intros s M.
    apply capmeta_ghost_tags_preserves, M.
  Qed.

  Instance memcpy_PreservesInvariant
    (loc: location_ocaml)
    (ptrval1 ptrval2: pointer_value)
    (size_int: integer_value)
    :
    forall s, PreservesInvariant mem_invariant s (memcpy loc ptrval1 ptrval2 size_int).
  Proof.
    intros s.
    unfold memcpy.
    remember (num_of_int size_int) as size.
    clear size_int Heqsize.

    apply bind_PreservesInvariant_value.
    intros M s' x AC.
    pose proof (memcpy_args_check_SameState loc ptrval1 ptrval2 size) as SA.
    specialize (SA _ _ _ AC).
    subst s'.
    split;[assumption|].
    destruct x.
    apply memcpy_arg_sane_after_check in AC.

    apply bind_PreservesInvariant_value.
    intros _ s' a1 H0.
    pose proof (serr2InternalErr_inv H0).
    apply serr2InternalErr_SameState in H0.
    subst s'.
    split;[assumption|].
    apply cap_addr_of_pointer_value_inv in H.
    destruct H as [c1 [P1 A1]].

    apply bind_PreservesInvariant_value.
    intros _ s' a2 H2.
    pose proof (serr2InternalErr_inv H2).
    apply serr2InternalErr_SameState in H2.
    subst s'.
    split;[assumption|].
    apply cap_addr_of_pointer_value_inv in H.
    destruct H as [c2 [P2 A2]].

    apply bind_PreservesInvariant_value.
    intros H s' x H0.
    destruct x.
    split.
    -
      pose proof (ghost_tags_PreservesInvariant a1 (Z.to_nat size) s H) as G.
      unfold post_exec_invariant, lift_sum_p, execErrS in G.
      break_let.
      repeat break_match_hyp.
      2,3: inv Heqs1.
      +
        tuple_inversion.
      +
        apply ret_inr in Heqs1.
        invc Heqs1.
        tuple_inversion.
        auto.
    -
      destruct (Z.eq_dec size 0) as [S0|SN0].
      +
        destruct size.
        2,3: inv S0.
        clear S0.
        Opaque ret.
        preserves_steps.
        *
          unfold memcpy_copy_data.
          replace (Z.to_nat 0) with O by lia.
          preserves_step.
          auto.
        *
          unfold memcpy_copy_tags.
          preserves_steps;bool_to_prop_hyp;try lia.
          exfalso.
          clear - Heqb0.
          pose proof MorelloImpl.alignof_pointer_pos.
          pose proof Z.mod_pos_bound (AddressValue.to_Z a1) (Z.of_nat (alignof_pointer MorelloImpl.get)).
          autospecialize H0. lia.
          zify.
          lia.
      +

        pose proof (ghost_tags_preserves_allocations _ _ _ _ H0).
        rewrite H1 in AC.
        apply bind_PreservesInvariant_value.
        intros H2 s'' x H3.
        destruct x.
        split.
        *
          pose proof (memcpy_copy_data_PreservesInvariant loc a1 a2 (Z.to_nat size) s') as P.
          autospecialize P.
          {
            intros a alignment aL aH H4 tg gs H5.
            apply capmeta_ghost_tags_spec_in_extended
              with (a:=a) (addr:=a1) (size:=(Z.to_nat size))
                   (capmeta := (capmeta s)).
            -
              inv AC.
              lia.
            -
              auto.
            -
              replace (capmeta_ghost_tags a1 (Z.to_nat size) (capmeta s))
                with (capmeta s').
              apply H5.

              clear - H0.
              unfold ghost_tags in H0.
              apply update_mem_state_spec in H0.
              destruct s', s.
              cbn in *.
              invc H0.
              reflexivity.
          }
          specialize (P H2).

          unfold post_exec_invariant, lift_sum_p, execErrS in P.
          break_let.
          repeat break_match_hyp.
          2,3: inv Heqs1.
          --
            tuple_inversion.
          --
            apply ret_inr in Heqs1.
            invc Heqs1.
            tuple_inversion.
            auto.
        *
          pose proof (memcpy_copy_data_preserves_allocations _ _ _ _ _ _ H3).
          destruct M.
          epose proof (memcpy_copy_data_fetch_bytes_spec _ AC) as DS.
          preserves_step.
          eapply memcpy_copy_tags_PreservesInvariant
            with (ptrval1:=ptrval1) (ptrval2:=ptrval2)
          ; eauto.
          rewrite H4 in AC.
          apply AC.
          preserves_step.
          Unshelve.
          apply H2.
  Qed.

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

Misc:
va_*

 *)

End CheriMemoryImplWithProofs.
