Require Import Common.

Require Import AilTypes.

Lemma eq_integerBaseType_correct x y :
  boolSpec (eq_integerBaseType x y) (x = y).
Proof. destruct x, y; my_auto. Qed.

Lemma eq_integerType_correct x y :
  boolSpec (eq_integerType x y) (x = y).
Proof.
  destruct x, y; simpl;
  match goal with
  | |- context[eq_integerBaseType ?x ?y] => set (eq_integerBaseType_correct x y); boolSpec_destruct
  | _ => idtac
  end; my_auto.
Qed.

Ltac destruct_integerType_hyp H :=
  let ibt := fresh in
  destruct H as [| |ibt|ibt];
  try destruct ibt.

Ltac destruct_integerBaseType :=
  repeat match goal with
  | [ ibt : integerBaseType |- _] => destruct ibt
  end.

Ltac destruct_integerType :=
  repeat match goal with
  | [ it  : integerType     |- _] => destruct it
  | [ ibt : integerBaseType |- _] => destruct ibt
  end.

Ltac clear_integerType :=
  repeat match goal with
  | [ it  : integerType     |- _] => clear dependent it
  | [ ibt : integerBaseType |- _] => clear dependent ibt
end.

Lemma eq_qualifiers_correct x y :
  boolSpec (eq_qualifiers x y) (x = y).
Proof.
  repeat match goal with
  | q : qualifiers |- _ => destruct q
  | b : bool       |- _ => destruct b
  end; my_auto.
Qed.

Lemma eq_basicType_correct x y :
  boolSpec (eq_basicType x y) (x = y).
Proof.
  destruct x, y; simpl;
  match goal with
  | |- context[eq_integerType ?x ?y] => set (eq_integerType_correct x y); boolSpec_destruct
  | _ => idtac
  end; my_auto.
Qed.

Definition ctype_nrect
         (P : ctype -> Type)
         (Q : list (qualifiers * ctype) -> Type)

         (Hnil      : Q nil)
         (Hcons     : forall {q} {t} {p}, P t -> Q p -> Q (cons (q,t) p))

         (HVoid     : P Void)
         (HBasic    : forall {bt}, P (Basic bt))
         (HArray    : forall {t} {n}, P t -> P (Array t n))
         (HFunction : forall {t} {p}, P t -> Q p -> P (Function t p))
         (HPointer  : forall {q : qualifiers} {t : ctype}, P t -> P (Pointer q t)) :
  forall t, P t
:=
  fix f t : P t :=
    match t return P t with
    | Void         => HVoid
    | Basic    _   => HBasic
    | Array    _ _ => HArray    (f _)
    | Function _ p => let fix g p : Q p :=
                        match p return Q p with
                        | nil          => Hnil
                        | cons (_,t) p => Hcons (f t) (g p)
                        end in
                      HFunction (f _) (g _)
    | Pointer  _ _ => HPointer  (f _)
    end.

Lemma eq_ctype_correct :
  forall x y, boolSpec (eq_ctype x y) (x = y).
Proof.
  apply (ctype_nrect (fun x => forall y, boolSpec (eq_ctype  x y) (x = y))
                     (fun x => forall y, boolSpec (eq_params x y) (x = y)));
  destruct y; simpl; fold eq_params;
  repeat (
    my_auto;
    match goal with
    | |- context[eq_basicType  ?x ?y] => set (eq_basicType_correct  x y)
    | |- context[eq_qualifiers ?x ?y] => set (eq_qualifiers_correct x y)
    | |- context[eq_nat        ?x ?y] => set (eq_nat_correct        x y)
    | H : forall _, boolSpec (eq_ctype  ?x _) _ |- context[eq_ctype  ?x ?y] => set (H y)
    | H : forall _, boolSpec (eq_params ?x _) _ |- context[eq_params ?x ?y] => set (H y)
    end;
    boolSpec_destruct
  ).
Qed.

Lemma eq_typeCategory_correct x y :
  boolSpec (eq_typeCategory x y) (x = y).
Proof.
  destruct x, y;
  repeat (
    my_auto;
    match goal with
    | |- context[eq_ctype      ?x ?y] => set (eq_ctype_correct      x y)
    | |- context[eq_qualifiers ?x ?y] => set (eq_qualifiers_correct x y)
    end;
    boolSpec_destruct
  ).
Qed.

Lemma eq_storageDuration_correct x y :
  boolSpec (eq_storageDuration x y) (x = y).
Proof. destruct x, y; my_auto. Qed.
