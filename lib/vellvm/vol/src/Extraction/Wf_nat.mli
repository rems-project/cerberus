open Datatypes

type __ = Obj.t

val induction_ltof1 :
  ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val induction_gtof1 :
  ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val induction_ltof2 :
  ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val induction_gtof2 :
  ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val lt_wf_rec1 : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1

val lt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1

val gt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1

val lt_wf_double_rec :
  (nat -> nat -> (nat -> nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1) ->
  nat -> nat -> 'a1

val iter_nat : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

