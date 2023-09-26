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

Require Import ListSet.

Module DummyTagDefs: TagDefs.
  Definition tagDefs (_:unit) := SymMap.empty CoqCtype.tag_definition.
End DummyTagDefs.

Module RevocationProofs.

  Fixpoint remove_PNVI (x:cerb_switches_t) : cerb_switches_t :=
    match x with
    | nil => empty_set _
    | SW_PNVI _ :: xs => remove_PNVI xs
    | x :: xs => x :: remove_PNVI xs
    end.

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
    Include CheriMemoryImpl(Capability_GS)(MorelloImpl)(DummyTagDefs)(WithoutPNVISwitches).
  End CheriMemoryWithoutPNVI.

  Module CheriMemoryWithPNVI.
    Include CheriMemoryImpl(Capability_GS)(MorelloImpl)(DummyTagDefs)(WithPNVISwitches).
  End CheriMemoryWithPNVI.

(*  Theorem foo:
    forall t,
      CheriMemoryWithoutPNVI.null_ptrval t <> CheriMemoryWithPNVI.null_ptrval t.
*)
End RevocationProofs.
