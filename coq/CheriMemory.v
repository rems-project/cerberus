Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.

Require Import Memory_model.

Module CheriAddr: MADDR.
  Definition t := Z.

  Definition bitwise_complement (n:Z) := n. (* TODO *)

  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Definition ltb_irref := Z.ltb_irrefl.
End CheriAddr.
