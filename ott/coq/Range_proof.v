Require Import Common.

Require Import ZArith.
Local Open Scope Z_scope.

Require Import Range_defns Range.

Lemma max_make_range {x y} {p : x <= y} : max (make_range p) = y.
Proof. reflexivity. Defined.  

Lemma min_make_range {x y} {p : x <= y} : min (make_range p) = x.
Proof. reflexivity. Defined.

Definition noOverlap_False {r1 r2} : ~max r1 <= min r2 -> ~max r2 <= min r1 ->  noOverlap r1 r2 -> False.
Proof. intros ? ?; destruct 1; contradiction. Defined.

Lemma no_overlap_correct r1 r2 : boolSpec (no_overlap r1 r2) (noOverlap r1 r2).
Proof.
  do 2 unfold_goal.
  set (Z.leb (max r1) (min r2)) as is_below.
  set (Z.leb (max r2) (min r1)) as is_above.
  case_eq is_below; intros Hr1r2;
    [ set        (Zle_bool_imp_le _ _  Hr1r2)
    | set (proj1 (Z.leb_nle       _ _) Hr1r2) ].
  + constructor 1; assumption.
  + case_eq is_above; intros Hr2r1;
      [ set        (Zle_bool_imp_le _ _  Hr2r1)
      | set (proj1 (Z.leb_nle       _ _) Hr2r1) ].
    - constructor 2; assumption.
    - inversion 1; contradiction.
Defined.

Lemma sub_correct r1 r2 : boolSpec (sub r1 r2) (Range_defns.sub r1 r2).
Proof.
  do 2 unfold_goal.
  set (Z.leb (max r1) (max r2)) as is_le_max.
  set (Z.leb (min r2) (min r1)) as is_ge_min.
  case_eq is_le_max; intros Hr1r2;
    [ set        (Zle_bool_imp_le _ _  Hr1r2)
    | set (proj1 (Z.leb_nle       _ _) Hr1r2) ].
  + case_eq is_ge_min; intros Hr2r1;
      [ set        (Zle_bool_imp_le _ _  Hr2r1)
      | set (proj1 (Z.leb_nle       _ _) Hr2r1) ];
    my_auto.
  + my_auto.
Defined.

Lemma mem_correct w r : boolSpec (mem w r) (Range_defns.mem w r).
Proof.
  do 2 unfold_goal.
  set (Z.leb w (max r)) as is_le_max.
  set (Z.leb (min r) w) as is_ge_min.
  case_eq is_le_max; intros Hr1r2;
    [ set        (Zle_bool_imp_le _ _  Hr1r2)
    | set (proj1 (Z.leb_nle       _ _) Hr1r2) ].
  + case_eq is_ge_min; intros Hr2r1;
      [ set        (Zle_bool_imp_le _ _  Hr2r1)
      | set (proj1 (Z.leb_nle       _ _) Hr2r1) ];
    my_auto.
  + my_auto.
Defined.

Definition mem_nat_correct n r : boolSpec (mem_nat n r) (Range_defns.memNat n r) :=
  mem_correct (Z_of_nat n) r.
