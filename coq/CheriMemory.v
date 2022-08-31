Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.

Require Import Addr.
Require Import Memory_model.
Require Import Mem_common.
Require Import ErrorWithState.
Require Import Undefined.

Module CheriAddr: VADDR.
  Definition t := Z.

  Definition bitwise_complement (n:Z) := n. (* TODO *)

  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Definition ltb_irref := Z.ltb_irrefl.
End CheriAddr.

Local Open Scope string_scope.
Local Open Scope type_scope.


Module CheriMemory : Memory(CheriAddr).

  Include Mem_common(CheriAddr).

  Definition name := "CHERI memory model".

  Inductive MemMonadError :=
    | MemMonadErr: mem_error -> MemMonadError
    | MemMonadUB: (Location_ocaml_t * (list undefined_behaviour)) -> MemMonadError.

End CheriMemory.
