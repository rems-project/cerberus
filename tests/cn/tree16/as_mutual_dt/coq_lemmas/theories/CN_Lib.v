Require List.
Require Import ZArith Bool.
Require Import Lia.
Require NArith.

Definition wrapI (minInt : Z) (maxInt : Z) x :=
  let delta := (maxInt - minInt)%Z in
  let r := Z.modulo x delta in
  (if (r <=? maxInt) then r else r - delta)%Z.
