Require List.
Require Import ZArith Bool.

Fixpoint nth_list_enc {A L_A : Type}
    (dest : L_A -> option (A * L_A)) (i : nat) (xs : L_A) (d : A) :=
  match dest xs with
    | None => d
    | Some (y, ys) => match i with
      | 0%nat => y
      | S j => nth_list_enc dest j ys d
    end
  end.

Definition nth_list_z {A L_A : Type}
    (dest : L_A -> option (A * L_A)) (i : Z) (xs : L_A) (d : A) :=
  if (i <? 0)%Z then d
  else nth_list_enc dest (Z.to_nat i) xs d.


