Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
From Coq.Strings Require Import String Ascii HexString.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Equality. (* for dep. destruction *)
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Lia.

Require Import StructTact.StructTactics.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

From Coq.Lists Require Import List SetoidList. (* after exltlib *)

From CheriCaps.Morello Require Import Capabilities.
From CheriCaps.Common Require Import Capabilities.

From Common Require Import SimpleError Utils ZMap.
From Morello Require Import CapabilitiesGS MorelloCapsGS.

From CheriMemory Require Import CheriMorelloMemory Memory_model CoqMem_common ErrorWithState CoqUndefined ErrorWithState CoqLocation CoqSymbol CoqImplementation CoqTags CoqSwitches CerbSwitches CoqAilTypesAux.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Require Import AltBinNotations.
Import ListNotations.
Import MonadNotation.

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



Module RevocationProofs.

  (* --- Memory models instantiated with and without PNVI --- *)

  Definition remove_PNVI: cerb_switches_t -> cerb_switches_t :=
    List.filter (fun s => negb (is_PNVI_switch s)).

  (* Removes all other PNVI flavours *)
  Module WithoutPNVISwitches.
    Definition get_switches (_:unit) := remove_PNVI (abst_get_switches tt).
  End WithoutPNVISwitches.

  (* Adds [SW_PNVI AE_UDI] are removes all other PNVI flavours *)
  Module WithPNVISwitches.
    Definition get_switches (_:unit) :=
      ListSet.set_add cerb_switch_dec (SW_PNVI AE_UDI)
        (remove_PNVI (abst_get_switches tt)).
  End WithPNVISwitches.

  Module CheriMemoryWithoutPNVI: CheriMemoryImpl(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(WithoutPNVISwitches).
    Include CheriMemoryExe(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(WithoutPNVISwitches).
  End CheriMemoryWithoutPNVI.

  Module CheriMemoryWithPNVI:CheriMemoryImpl(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(WithPNVISwitches).
    Include CheriMemoryExe(MemCommonExe)(Capability_GS)(MorelloImpl)(CheriMemoryTypesExe)(AbstTagDefs)(WithPNVISwitches).
  End CheriMemoryWithPNVI.

  (* --- Equality predicates for types used in Memory Models --- *)

  Import CheriMemoryTypesExe.

  (* Equality of pointer values without taking provenance into account *)

  Inductive pointer_value_eq : pointer_value_ind -> pointer_value_ind -> Prop :=
  | pointer_value_no_prov_eq: forall pr1 pr2 b1 b2,  b1 = b2 -> pointer_value_eq (PV pr1 b1) (PV pr2 b2).

  Inductive mem_value_ind_eq: mem_value_ind -> mem_value_ind -> Prop :=
  | mem_value_ind_eq_MVunspecified: forall t1 t2, mem_value_ind_eq (MVunspecified t1) (MVunspecified t2)
  | mem_value_ind_eq_MVinteger: forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_ind_eq (MVinteger t1 v1) (MVinteger t2 v2)
  | mem_value_ind_eq_MVfloating: forall t1 t2 v1 v2, t1 = t2 /\ v1 = v2 -> mem_value_ind_eq (MVfloating t1 v1) (MVfloating t2 v2)
  | mem_value_ind_eq_MVpointer: forall t1 t2 p1 p2, t1 = t2 /\ pointer_value_eq p1 p2 -> mem_value_ind_eq (MVpointer t1 p1) (MVpointer t2 p2)
  | mem_value_ind_eq_MVarray: forall a1 a2, eqlistA mem_value_ind_eq a1 a2 -> mem_value_ind_eq (MVarray a1) (MVarray a2)
  | mem_value_ind_eq_MVstruct: forall tag_sym1 l1 tag_sym2 l2,
      tag_sym1 = tag_sym2  ->
      eqlistA struct_field_eq l1 l2 ->
      mem_value_ind_eq (MVstruct tag_sym1 l1) (MVstruct tag_sym2 l2)
  | mem_value_ind_eq_MVunion: forall tag_sym1 id1 v1 tag_sym2 id2 v2,
      tag_sym1 = tag_sym2 /\ id1 = id2 /\ mem_value_ind_eq v1 v2 ->
      mem_value_ind_eq (MVunion tag_sym1 id1 v1) (MVunion tag_sym2 id2 v2)
  with
    struct_field_eq: (CoqSymbol.identifier * CoqCtype.ctype * mem_value_ind) -> (CoqSymbol.identifier * CoqCtype.ctype * mem_value_ind) -> Prop :=
  | struct_field_triple_eq: forall id1 id2 t1 t2 v1 v2,
      id1 = id2 /\ t1 = t2 -> struct_field_eq (id1,t1,v1) (id2,t2,v2).


  (*       next_alloc_id : storage_instance_id;
      next_iota : symbolic_storage_instance_id;
      last_address : AddressValue.t;
      allocations : ZMap.t allocation;
      iota_map : ZMap.t
                   ((* `Single *) storage_instance_id +
                      (* `Double *) storage_instance_id * storage_instance_id);
      funptrmap : ZMap.t
                    (digest * string * C.t);
      varargs : ZMap.t
                  (Z * list (CoqCtype.ctype * pointer_value));
      next_varargs_id : Z;
      bytemap : ZMap.t AbsByte;
      capmeta : ZMap.t (bool* CapGhostState);
   *)

  Inductive ctype_pointer_value_eq: (CoqCtype.ctype * pointer_value_ind) ->
                                    (CoqCtype.ctype * pointer_value_ind) -> Prop
    :=
  | ctype_pointer_value_eq_1:
    forall t1 t2 pv1 pv2, t1 = t2 /\ pointer_value_eq pv1 pv2 ->
                     ctype_pointer_value_eq (t1,pv1) (t2,pv2).

  Inductive varargs_eq: (Z * list (CoqCtype.ctype * pointer_value_ind)) ->
                        (Z * list (CoqCtype.ctype * pointer_value_ind)) -> Prop :=
  | varargs_eq_1: forall z1 vl1 z2 vl2,
      z1 = z2 /\ eqlistA ctype_pointer_value_eq vl1 vl2
      -> varargs_eq (z1,vl1) (z2,vl2).

  Definition mem_state_same
    (a:CheriMemoryWithPNVI.mem_state_r)
    (b:CheriMemoryWithoutPNVI.mem_state_r): Prop
    :=
    a.(CheriMemoryWithPNVI.next_alloc_id) = b.(CheriMemoryWithoutPNVI.next_alloc_id)
    /\ a.(CheriMemoryWithPNVI.next_iota) = b.(CheriMemoryWithoutPNVI.next_iota)
    /\ a.(CheriMemoryWithPNVI.last_address) = b.(CheriMemoryWithoutPNVI.last_address)
    /\ ZMap.Equal a.(CheriMemoryWithPNVI.allocations) b.(CheriMemoryWithoutPNVI.allocations)
    /\ ZMap.Equal a.(CheriMemoryWithPNVI.iota_map) b.(CheriMemoryWithoutPNVI.iota_map)
    /\ ZMap.Equal a.(CheriMemoryWithPNVI.funptrmap) b.(CheriMemoryWithoutPNVI.funptrmap)
    /\ ZMap.Equiv varargs_eq a.(CheriMemoryWithPNVI.varargs) b.(CheriMemoryWithoutPNVI.varargs)
    /\ a.(CheriMemoryWithPNVI.next_varargs_id) = b.(CheriMemoryWithoutPNVI.next_varargs_id)
    /\ ZMap.Equal a.(CheriMemoryWithPNVI.bytemap) b.(CheriMemoryWithoutPNVI.bytemap)
    /\ ZMap.Equal a.(CheriMemoryWithPNVI.capmeta) b.(CheriMemoryWithoutPNVI.capmeta).

  Ltac destruct_mem_state_same H :=
    let Malloc_id := fresh "Malloc_id" in
    let Mnextiota := fresh "Mnextiota" in
    let Mlastaddr := fresh "Mlastaddr" in
    let Mallocs := fresh "Mallocs" in
    let Miotas := fresh "Miotas" in
    let Mfuncs := fresh "Mfuncs" in
    let Mvarargs := fresh "Mvarargs" in
    let Mnextvararg := fresh "Mnextvararg" in
    let Mbytes := fresh "Mbytes" in
    let Mcapmeta := fresh "Mcapmeta" in
    destruct H as (Malloc_id & Mnextiota & Mlastaddr & Mallocs & Miotas & Mfuncs & Mvarargs & Mnextvararg & Mbytes & Mcapmeta).

  (* Equivalence relation for pointer values *)
  #[local] Instance pointer_value_Equivalence : Equivalence(pointer_value_eq).
  Proof.
    split.
    -
      intros a.
      destruct a.
      apply pointer_value_no_prov_eq.
      reflexivity.
    -
      intros a b.
      destruct a, b.
      intros H.
      apply pointer_value_no_prov_eq.
      inversion H.
      auto.
    -
      intros a b c.
      destruct a, b, c.
      intros H1 H2.
      apply pointer_value_no_prov_eq.
      inversion H1. clear H1.
      inversion H2. clear H2.
      subst.
      reflexivity.
  Qed.

  (* --- Helper lemmas *)
  Lemma is_PNVI_WithPNVI:
    is_PNVI (WithPNVISwitches.get_switches tt) = true.
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

  Lemma is_PNVI_WithoutPNVI:
    is_PNVI (WithoutPNVISwitches.get_switches tt) = false.
  Proof.
    unfold WithoutPNVISwitches.get_switches.
    remember (abst_get_switches tt) as l.
    unfold is_PNVI, remove_PNVI in *.
    apply Bool.not_true_is_false.
    intros E.
    apply Bool.Is_true_eq_left in E.
    apply list.existb_True in E.
    apply Exists_exists in E.
    destruct E as [x [H0 H1]].
    apply filter_In in H0.
    destruct H0 as [H2 H3].
    apply Bool.negb_true_iff in H3.
    rewrite H3 in H1.
    inversion H1.
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


  Lemma remove_PNVI_set_mem:
    forall l s,
      is_PNVI_switch s = false ->
      set_mem cerb_switch_dec s (remove_PNVI l) =
        set_mem cerb_switch_dec s l.
  Proof.
    intros l s H.
    apply Bool.eqb_prop.
    unfold Bool.eqb.
    break_if;break_if;auto.
    -
      apply set_mem_correct1 in Heqb.
      apply set_mem_complete1 in Heqb0.
      apply remove_PNVI_In in Heqb;auto.
    -
      apply set_mem_correct1 in Heqb0.
      apply set_mem_complete1 in Heqb.
      apply remove_PNVI_In in Heqb0;auto.
  Qed.


  (* All non-pnvi switches are the same *)
  Lemma non_PNVI_switches_match:
    forall s,
      is_PNVI_switch s = false ->
      has_switch (WithPNVISwitches.get_switches tt) s =
        has_switch (WithoutPNVISwitches.get_switches tt) s.
  Proof.
    intros s H.
    unfold WithPNVISwitches.get_switches.
    unfold WithoutPNVISwitches.get_switches.
    generalize (abst_get_switches tt) as l.
    intros l.
    pose proof (set_In_dec cerb_switch_dec s l) as D.
    unfold is_PNVI_switch in H.

    Ltac one_has_switch D :=
      unfold has_switch;
      rewrite remove_PNVI_set_mem by auto;
      destruct D as [IN | NIN];
      [ apply set_mem_correct2 with (Aeq_dec:=cerb_switch_dec) in IN;
        rewrite IN;
        apply set_mem_correct2, set_add_intro1;
        apply -> remove_PNVI_In;
        [ apply set_mem_correct1 with (Aeq_dec:=cerb_switch_dec);
          assumption
        | auto ]
      | apply set_mem_complete2 with (Aeq_dec:=cerb_switch_dec) in NIN;
        rewrite NIN;
        apply set_mem_complete2;
        intros H;
        apply set_add_elim2 in H; auto;
        apply remove_PNVI_In in H;
        [ apply set_mem_correct2 with (Aeq_dec:=cerb_switch_dec) in H;
          congruence
        | auto ]
      ].

    destruct s eqn:S; inversion H; clear H; one_has_switch D.
  Qed.

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
    forall t,
      pointer_value_eq
        (CheriMemoryWithPNVI.null_ptrval t)
        (CheriMemoryWithoutPNVI.null_ptrval t).
  Proof.
    intros t.
    apply pointer_value_no_prov_eq.
    reflexivity.
  Qed.

  Theorem concrete_ptrval_same:
    forall n a,
      serr_eq pointer_value_eq
        (CheriMemoryWithPNVI.concrete_ptrval n a)
        (CheriMemoryWithoutPNVI.concrete_ptrval n a).
  Proof.
    reflexivity.
  Qed.

  Theorem fun_ptrval_same:
    forall s,
      serr_eq pointer_value_eq
        (CheriMemoryWithPNVI.fun_ptrval s)
        (CheriMemoryWithoutPNVI.fun_ptrval s).
  Proof.
    intros s.
    apply pointer_value_no_prov_eq.
    reflexivity.
  Qed.

  Theorem case_funsym_opt_same:
    forall m1 m2 p1 p2,
      mem_state_same m1 m2 ->
      pointer_value_eq p1 p2 ->
      (CheriMemoryWithPNVI.case_funsym_opt m1 p1 =
         CheriMemoryWithoutPNVI.case_funsym_opt m2 p2).
  Proof.
    cbn.
    intros m1 m2 [p1prov p1v] [p2prov p2v] ME FE.
    inversion FE. clear FE.
    unfold CheriMemoryWithPNVI.case_funsym_opt, CheriMemoryWithPNVI.break_PV.
    unfold CheriMemoryWithoutPNVI.case_funsym_opt, CheriMemoryWithoutPNVI.break_PV.
    destruct p1v, p2v.
    clear p1prov p2prov pr1 pr2 H H2.
    -
      inversion H0.
      clear f H0 H1 H2.
      destruct f0.
      +
        reflexivity.
      +
        unfold CheriMemoryWithPNVI.cap_to_Z, CheriMemoryWithoutPNVI.cap_to_Z.
        pose models_compatible as C.
        destruct C as [CI _].
        rewrite CI.

        destruct_mem_state_same ME.
        unfold ZMap.Equal in Mfuncs.
        rewrite Mfuncs.
        reflexivity.
    -
      inversion H0.
    -
      inversion H0.
    -
      inversion H0.
      clear H0 t H5 H1.
      destruct_mem_state_same ME.
      unfold ZMap.Equal in Mfuncs.
      rewrite Mfuncs.
      reflexivity.
  Qed.

  Theorem derive_cap_same:
    forall is_signed bop ival1 ival2,
      CheriMemoryWithPNVI.derive_cap is_signed bop ival1 ival2 =
        CheriMemoryWithoutPNVI.derive_cap is_signed bop ival1 ival2.
  Proof.
    reflexivity.
  Qed.

  Theorem cap_assign_value_same:
    forall loc ival_cap ival_n,
      CheriMemoryWithPNVI.cap_assign_value loc ival_cap ival_n =
        CheriMemoryWithoutPNVI.cap_assign_value loc ival_cap ival_n.
  Proof.
    reflexivity.
  Qed.

  Theorem ptr_t_int_value_same:
    forall p,
      CheriMemoryWithPNVI.ptr_t_int_value p =
        CheriMemoryWithoutPNVI.ptr_t_int_value p.
  Proof.
    reflexivity.
  Qed.

  Theorem null_cap_same:
    forall f,
      CheriMemoryWithPNVI.null_cap f =
        CheriMemoryWithoutPNVI.null_cap f.
  Proof.
    reflexivity.
  Qed.

  Theorem array_shift_ptrval_same:
    forall pv ct iv,
      CheriMemoryWithPNVI.array_shift_ptrval pv ct iv =
        CheriMemoryWithoutPNVI.array_shift_ptrval pv ct iv.
  Proof.
    reflexivity.
  Qed.

  Theorem member_shift_ptrval_same:
    forall pv ct ci,
      CheriMemoryWithPNVI.member_shift_ptrval pv ct ci =
        CheriMemoryWithoutPNVI.member_shift_ptrval pv ct ci.
  Proof.
    reflexivity.
  Qed.

  Theorem concurRead_ival_same:
    forall ct cs,
      CheriMemoryWithPNVI.concurRead_ival ct cs =
        CheriMemoryWithoutPNVI.concurRead_ival ct cs.
  Proof.
    reflexivity.
  Qed.

  Theorem integer_ival_same:
    forall n,
      CheriMemoryWithPNVI.integer_ival n =
        CheriMemoryWithoutPNVI.integer_ival n.
  Proof.
    reflexivity.
  Qed.

  Theorem max_ival_same:
    forall ct,
      CheriMemoryWithPNVI.max_ival ct =
        CheriMemoryWithoutPNVI.max_ival ct.
  Proof.
    reflexivity.
  Qed.

  Theorem min_ival_same:
    forall ct,
      CheriMemoryWithPNVI.min_ival ct =
        CheriMemoryWithoutPNVI.min_ival ct.
  Proof.
    reflexivity.
  Qed.

  Theorem op_ival_same:
    forall op a b,
      CheriMemoryWithPNVI.op_ival op a b =
        CheriMemoryWithoutPNVI.op_ival op a b.
  Proof.
    reflexivity.
  Qed.

  (* TODO: requires `offsetof_same`
  Theorem offsetof_ival_same:
    forall tagDefs tag_sym memb_ident,
      CheriMemoryWithPNVI.offsetof_ival tagDefs tag_sym memb_ident =
        CheriMemoryWithoutPNVI.offsetof_ival tagDefs tag_sym memb_ident.
  Proof.
    intros tagDefs tag_sym memb_ident.

  Admitted.
   *)

  (* TODO:
    Definition sizeof_ival (ty : CoqCtype.ctype): serr integer_value
    depends on stateful
   *)

  (* TODO:
  Definition alignof_ival (ty: CoqCtype.ctype): serr integer_value
    depends on stateful
   *)

  Theorem bitwise_complement_ival_same:
    forall ty v,
      CheriMemoryWithPNVI.bitwise_complement_ival ty v =
        CheriMemoryWithoutPNVI.bitwise_complement_ival ty v.
  Proof.
    reflexivity.
  Qed.

  Theorem bitwise_and_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_and_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_and_ival ty a b.
  Proof.
    reflexivity.
  Qed.

  Theorem bitwise_or_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_or_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_or_ival ty a b.
  Proof.
    reflexivity.
  Qed.

  Theorem bitwise_xor_ival_same:
    forall ty a b,
      CheriMemoryWithPNVI.bitwise_xor_ival ty a b =
        CheriMemoryWithoutPNVI.bitwise_xor_ival ty a b.
  Proof.
    reflexivity.
  Qed.

  Theorem is_specified_ival_same:
    forall v,
      CheriMemoryWithPNVI.is_specified_ival v =
        CheriMemoryWithoutPNVI.is_specified_ival v.
  Proof.
    reflexivity.
  Qed.

  Theorem eq_ival_same:
    forall a b,
      CheriMemoryWithPNVI.eq_ival a b =
        CheriMemoryWithoutPNVI.eq_ival a b.
  Proof.
    reflexivity.
  Qed.

  Theorem lt_ival_same:
    forall a b,
      CheriMemoryWithPNVI.lt_ival a b =
        CheriMemoryWithoutPNVI.lt_ival a b.
  Proof.
    reflexivity.
  Qed.

  Theorem le_ival_same:
    forall a b,
      CheriMemoryWithPNVI.le_ival a b =
        CheriMemoryWithoutPNVI.le_ival a b.
  Proof.
    reflexivity.
  Qed.

  Theorem str_fval_same:
    forall v,
      CheriMemoryWithPNVI.str_fval v =
        CheriMemoryWithoutPNVI.str_fval v.
  Proof.
    reflexivity.
  Qed.

  Definition op_fval_same:
    forall fop a b,
      CheriMemoryWithPNVI.op_fval fop a b =
        CheriMemoryWithoutPNVI.op_fval fop a b.
  Proof.
    reflexivity.
  Qed.

  Theorem eq_fval_same:
    forall a b,
      CheriMemoryWithPNVI.eq_fval a b =
        CheriMemoryWithoutPNVI.eq_fval a b.
  Proof.
    reflexivity.
  Qed.

  Theorem lt_fval_same:
    forall a b,
      CheriMemoryWithPNVI.lt_fval a b =
        CheriMemoryWithoutPNVI.lt_fval a b.
  Proof.
    reflexivity.
  Qed.

  Theorem le_fval_same:
    forall a b,
      CheriMemoryWithPNVI.le_fval a b =
        CheriMemoryWithoutPNVI.le_fval a b.
  Proof.
    reflexivity.
  Qed.

  Theorem fvfromint_same:
    forall v,
      CheriMemoryWithPNVI.fvfromint v =
        CheriMemoryWithoutPNVI.fvfromint v.
  Proof.
    reflexivity.
  Qed.

  Theorem ivfromfloat_same:
    forall t v,
      CheriMemoryWithPNVI.ivfromfloat t v =
        CheriMemoryWithoutPNVI.ivfromfloat t v.
  Proof.
    reflexivity.
  Qed.

  Theorem unspecified_mval_same:
    forall t,
      CheriMemoryWithPNVI.unspecified_mval t =
        CheriMemoryWithoutPNVI.unspecified_mval t.
  Proof.
    reflexivity.
  Qed.

  Theorem integer_value_mval_same:
    forall t v,
      CheriMemoryWithPNVI.integer_value_mval t v =
        CheriMemoryWithoutPNVI.integer_value_mval t v.
  Proof.
    reflexivity.
  Qed.

  Theorem floating_value_mval_same:
    forall t v,
      CheriMemoryWithPNVI.floating_value_mval t v =
        CheriMemoryWithoutPNVI.floating_value_mval t v.
  Proof.
    reflexivity.
  Qed.

  (* This theorem using weaker equality, since pointers are involved *)
  Theorem pointer_mval_same:
    forall t p1 p2,
      pointer_value_eq p1 p2 ->
      mem_value_ind_eq (CheriMemoryWithPNVI.pointer_mval t p1)
        (CheriMemoryWithoutPNVI.pointer_mval t p2).
  Proof.
    intros t p1 p2 H.
    constructor.
    auto.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem array_mval_same:
    forall a1 a2,
      eqlistA mem_value_ind_eq a1 a2 ->
      mem_value_ind_eq (CheriMemoryWithPNVI.array_mval a1)
        (CheriMemoryWithoutPNVI.array_mval a2).
  Proof.
    intros a1 a2 H.
    constructor.
    assumption.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem struct_mval_same:
    forall s1 s2 l1 l2,
      s1 = s2 /\ eqlistA struct_field_eq l1 l2 ->
      mem_value_ind_eq (CheriMemoryWithPNVI.struct_mval s1 l1)
        (CheriMemoryWithoutPNVI.struct_mval s2 l2).
  Proof.
    intros s1 s2 l1 l2 [H1 H2].
    constructor; assumption.
  Qed.

  (* This theorem using weaker equality, since pointers may be involved *)
  Theorem union_mval_same:
    forall s1 id1 v1 s2 id2 v2,
      s1 = s2 /\ id1 = id2 /\ mem_value_ind_eq v1 v2 ->
      mem_value_ind_eq (CheriMemoryWithPNVI.union_mval s1 id1 v1)
        (CheriMemoryWithoutPNVI.union_mval s2 id2 v2).
  Proof.
    intros s1 id1 v1 s2 id2 v2 H.
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
    repeat break_if; auto.

    rewrite non_PNVI_switches_match in Heqb0.
    congruence.
    reflexivity.

    rewrite non_PNVI_switches_match in Heqb0.
    congruence.
    reflexivity.
  Qed.

  (* Stateful proofs below *)

  Definition lift_sum
    {A1 A2 B1 B2 C:Type}
    (fl: A1->A2->C) (fr:B1->B2->C)
    (default: C)
    (a:sum A1 B1) (b:sum A2 B2): C :=
    match a,b with
    | inl l1, inl l2 => fl l1 l2
    | inr r1, inr r2 => fr r1 r2
    | _, _ => default
    end.

  #[local] Instance zmap_range_init_Proper:
    forall [elt : Type], Proper (eq ==> eq ==> eq ==> eq ==> ZMap.Equal ==> ZMap.Equal) (zmap_range_init (T:=elt)).
  Proof.
    intros elt a1 a0 EA n0 n EN s0 s ES v0 v EV m0 m1 EM k.
    subst.
    dependent induction n.
    -
      cbn.
      apply EM.
    -
      cbn.
      apply IHn.
      apply F.add_m;auto.
  Qed.

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

  Lemma AddressValue_Z_id:
    forall a,
      AddressValue.of_Z (AddressValue.to_Z a) = a.
  Proof.
    intros a.
    unfold AddressValue.t, AddressValue.of_Z, AddressValue.to_Z in *.
    unfold bv_to_Z_unsigned.
    apply bitvector.Z_to_bv_bv_unsigned.
  Qed.

  Theorem allocator_same:
    forall mem_state1 mem_state2 size align,
      mem_state_same mem_state1 mem_state2 ->
      evalErrS (CheriMemoryWithPNVI.allocator size align) mem_state1 =
        evalErrS (CheriMemoryWithoutPNVI.allocator size align) mem_state2
      /\
        lift_sum eq mem_state_same False
          (execErrS (CheriMemoryWithPNVI.allocator size align) mem_state1)
          (execErrS (CheriMemoryWithoutPNVI.allocator size align) mem_state2).
  Proof.
    intros mem_state1 mem_state2 sz align M.
    destruct_mem_state_same M.
    split.
    - (* return value *)
      unfold evalErrS.
      unfold CheriMemoryWithPNVI.allocator, CheriMemoryWithoutPNVI.allocator.
      unfold put, ret, bind.
      cbn.
      repeat break_let.
      unfold CheriMemoryWithPNVI.memM in *.
      unfold CheriMemoryWithPNVI.mem_state in *.
      repeat break_if; repeat break_match;
      repeat tuple_inversion;
        rewrite Mlastaddr in *; try congruence; try reflexivity.
      +
        rewrite <- Malloc_id in *.
        rewrite  Heqp1 in Heqp4.
        tuple_inversion.
        reflexivity.
      +
        rewrite <- Malloc_id in *.
        rewrite  Heqp1 in Heqp4.
        tuple_inversion.
        reflexivity.
    - (* state *)
      unfold lift_sum.
      unfold CheriMemoryWithPNVI.mem_state in *.
      unfold execErrS.
      repeat break_let.
      repeat break_match;invc Heqs1;invc Heqs0.
      all: cbn in Heqp, Heqp0; repeat break_let.
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
        *
          cbn.
          repeat break_let.
          apply init_ghost_tags_same.
          assumption.
        *
          cbn.
          repeat break_let.
          apply init_ghost_tags_same.
          assumption.
  Qed.

End RevocationProofs.
