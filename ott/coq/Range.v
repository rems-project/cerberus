Require Import ZArith.
Local Open Scope Z_scope.

Definition range := {p : Z * Z | fst p <= snd p}.

Definition min (r : range) := fst (proj1_sig r).
Definition max (r : range) := snd (proj1_sig r).

Definition make_range {x y} : x <= y -> range :=
  fun p => exist _ (x, y) p.

Definition no_overlap (r1 r2 : range) : bool :=
  let is_below := Z.leb (max r1) (min r2) in
  let is_above := Z.leb (max r2) (min r1) in
  match is_below, is_above with
  | true, _    => true
  | _   , true => true
  | _   , _    => false
  end.

Definition sub (r1 r2 : range) : bool :=
  let is_le_max := Z.leb (max r1) (max r2) in
  let is_ge_min := Z.leb (min r2) (min r1) in
  match is_le_max, is_ge_min with
  | true, true    => true
  | _   , _       => false
  end.

Definition mem w r : bool :=
  let is_le_max := Z.leb w (max r) in
  let is_ge_min := Z.leb (min r) w in
  match is_le_max, is_ge_min with
  | true, true => true
  | _   , _    => false
  end.

Definition mem_nat n r : bool := mem (Z_of_nat n) r.
