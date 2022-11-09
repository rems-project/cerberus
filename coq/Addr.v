From stdpp.unstable Require Import bitvector. 

Require Import Coq.Numbers.BinNums.

Module Type VADDR.
  Parameter Inline t:Set.

  Parameter bitwise_complement: Z -> Z.

  Parameter eqb: t -> t -> bool.
  Parameter ltb: t -> t -> bool.
  Parameter leb: t -> t -> bool.
  Parameter ltb_irref: forall a:t, ltb a a = false.

  Parameter of_Z: Z -> t.
  Parameter to_Z: t -> Z.

End VADDR.
