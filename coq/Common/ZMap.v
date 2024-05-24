(** Map indexed by [Z] *)

Require Import Coq.ZArith.BinInt.
Require Import Coq.Structures.OrderedTypeEx.

Require Import FMapExt.

Module Z_as_ExtOT : OrderedTypeExt with Definition t:=Z.
  Include Z_as_OT.

  Definition with_offset := Z.add.
  Definition of_nat := Z.of_nat.
  Definition of_Z (x:Z) := x.

End Z_as_ExtOT.

Module ZMap <: FMapExt Z_as_ExtOT.
  Include FMapExt.FMapExt(Z_as_ExtOT).
End ZMap.
