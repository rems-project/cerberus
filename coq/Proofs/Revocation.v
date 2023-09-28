Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
From Coq.Strings Require Import String Ascii HexString.
Require Import Lia.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

From Coq.Lists Require Import List. (* after exltlib *)

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

  Module CheriMemoryWithoutPNVI.
    Include CheriMemoryImpl(Capability_GS)(MorelloImpl)(AbstTagDefs)(WithoutPNVISwitches).
  End CheriMemoryWithoutPNVI.

  Module CheriMemoryWithPNVI.
    Include CheriMemoryImpl(Capability_GS)(MorelloImpl)(AbstTagDefs)(WithPNVISwitches).
  End CheriMemoryWithPNVI.

  (* --- Equality predicates for types used in Memory Models --- *)

  Definition function_pointer_eq
    (a:CheriMemoryWithPNVI.function_pointer)
    (b:CheriMemoryWithoutPNVI.function_pointer)
    :=
    match a,b with
    | CheriMemoryWithPNVI.FP_valid s1, CheriMemoryWithoutPNVI.FP_valid s2 => s1 = s2
    | CheriMemoryWithPNVI.FP_invalid c1, CheriMemoryWithoutPNVI.FP_invalid c2 => c1 = c2
    | _, _ => False
    end.

  Definition pointer_value_base_eq
    (a:CheriMemoryWithPNVI.pointer_value_base)
    (b:CheriMemoryWithoutPNVI.pointer_value_base)
    :=
    match a,b with
    | CheriMemoryWithPNVI.PVfunction f1, CheriMemoryWithoutPNVI.PVfunction f2 => function_pointer_eq f1 f2
    | CheriMemoryWithPNVI.PVconcrete c1, CheriMemoryWithoutPNVI.PVconcrete c2 => c1 = c2
    | _, _ => False
    end.

  Definition provenance_eq
    (a:CheriMemoryWithPNVI.provenance)
    (b:CheriMemoryWithoutPNVI.provenance) : Prop
    :=
    match a,b with
    | CheriMemoryWithPNVI.Prov_disabled, CheriMemoryWithoutPNVI.Prov_disabled => True
    | CheriMemoryWithPNVI.Prov_none, CheriMemoryWithoutPNVI.Prov_none => True
    | CheriMemoryWithPNVI.Prov_some id1, CheriMemoryWithoutPNVI.Prov_some id2 =>
        id1 = id2
    | CheriMemoryWithPNVI.Prov_symbolic sid1, CheriMemoryWithoutPNVI.Prov_symbolic sid2 =>
        sid1 = sid2
    | CheriMemoryWithPNVI.Prov_device, CheriMemoryWithoutPNVI.Prov_device => True
    | _, _ => False
    end.

  (* Compare pointer values without taking provenance into account *)
  Definition pointer_value_eq
    (a:CheriMemoryWithPNVI.pointer_value)
    (b:CheriMemoryWithoutPNVI.pointer_value) : Prop
    :=
    match a,b with
    | CheriMemoryWithPNVI.PV p1 b1, CheriMemoryWithoutPNVI.PV p2 b2 =>
        (* provenance_eq p1 p2 /\ *) pointer_value_base_eq b1 b2
    end.

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

  (* --- Lemmas about memory models --- *)

  Theorem null_ptrval_same:
    forall t,
      pointer_value_eq
        (CheriMemoryWithPNVI.null_ptrval t)
        (CheriMemoryWithoutPNVI.null_ptrval t).
  Proof.
    reflexivity.
  Qed.

End RevocationProofs.
