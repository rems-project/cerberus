Require Import Coq.Program.Equality.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.

Require Import StructTact.StructTactics.

Require Import Coq.Arith.Arith.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Sym.
Require Import Id.

Inductive sign : Type :=
  | Signed
  | Unsigned.

Unset Elimination Schemes.
Inductive t_gen (A:Type) : Type :=
  (* base cases *)
  | Unit : t_gen A  
  | Bool : t_gen A
  | Integer : t_gen A
  | MemByte : t_gen A
  | Bits : sign -> nat -> t_gen A
  | Real : t_gen A
  | Alloc_id : t_gen A
  | Loc : A -> t_gen A
  | CType : t_gen A
  | Struct : Sym.t -> t_gen A
  | Datatype : Sym.t -> t_gen A
  (* recursive cases *)
  | TRecord : list (Symbol.identifier * t_gen A) -> t_gen A
  | Map : t_gen A -> t_gen A -> t_gen A
  | List : t_gen A -> t_gen A
  | Tuple : list (t_gen A) -> t_gen A
  | TSet : t_gen A -> t_gen A.
Set Elimination Schemes.

Inductive Forall_type {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil : Forall_type P nil
| Forall_cons : forall (x : A) (xs : list A), P x -> Forall_type P xs -> Forall_type P (x :: xs).

(* We define a custom induction principle for [t_gen] because the
   default one incorrectly handles hidden recursive cases for the
   [TFunction] and [Tuple] constructors. *)
Theorem t_gen_ind_set (A : Type) (P : t_gen A -> Type):
  (* base cases *)
  P (Unit A) ->
  P (Bool A) ->
  P (Integer A) ->
  P (MemByte A) ->
  (forall (s : sign) (n : nat), P (Bits A s n)) ->
  P (Real A) ->
  P (Alloc_id A) ->
  (forall a : A, P (Loc A a)) ->
  P (CType A) ->
  (forall t : Sym.t, P (Struct A t)) ->
  (forall t : Sym.t, P (Datatype A t)) ->
  (* recursive cases *)
  (forall l : list (Symbol.identifier * t_gen A), (Forall_type (fun '(_,x) => P x) l) -> P (TRecord A l)) ->
  (forall t : t_gen A, P t -> forall t0 : t_gen A, P t0 -> P (Map A t t0)) ->
  (forall t : t_gen A, P t -> P (List A t)) ->
  (forall l : list (t_gen A), (Forall_type P l) -> P (Tuple A l))  ->
  (forall t : t_gen A, P t -> P (TSet A t))

  -> forall t : t_gen A, P t.
Proof.
  intros HUnit HBool HInteger HMemByte HBits HReal HAlloc HLoc HCType HStruct HDatatype HTRecord HMap HList HTuple HTSet.
  fix IH 1.
  intros t.
  destruct t; simpl.
  - (* Unit *)
    apply HUnit.
  - (* Bool *)
    apply HBool.
  - (* Integer *)
    apply HInteger.
  - (* MemByte *)
    apply HMemByte.
  - (* Bits *)
    apply HBits.
  - (* Real *)
    apply HReal.
  - (* Alloc_id *)
    apply HAlloc.
  - (* Loc *)
    apply HLoc.
  - (* CType *)
    apply HCType.
  - (* Struct *)
    apply HStruct.
  - (* Datatype *)
    apply HDatatype.
  - (* TRecord *)
    eapply HTRecord.
    induction l.
    + constructor.
    + constructor.
      break_let.
      auto.
      auto.
  - (* Map *)
    apply HMap; apply IH.
  - (* List *)
    apply HList; apply IH.
  - (* Tuple *)
    eapply HTuple.
    induction l.
    + constructor.
    + constructor; auto.
  - (* TSet *)
    apply HTSet; apply IH.
Qed.


Definition member_types_gen (A:Type) := list (Id.t * t_gen A).

Module Datatype.
  Record info (A : Type) := mk_info {
    constrs : list Sym.t;
    all_params : member_types_gen A
  }.

  Record constr_info (A : Type) := mk_constr_info {
    params : member_types_gen A;
    datatype_tag : Sym.t
  }.
End Datatype.

Definition t := t_gen unit.

Fact sign_eq_dec (s1 s2 : sign) : {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

(* TODO Check if needed *)
Lemma prod_eq_dec {A B : Type}
      (eqA : forall x y : A, {x = y} + {x <> y})
      (eqB : forall x y : B, {x = y} + {x <> y}) :
      forall (p1 p2 : A * B), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Qed.

Module BasetTypes_t_as_MiniDecidableType <: MiniDecidableType.
  Definition t := t.
  Definition eq := @eq t.
  
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq, t, BaseTypes.t.
    intros x.
    apply (t_gen_ind_set unit (fun t => forall y, { t = y } + { t <> y })).

    (* fragile: assuming `y` *)
    all: intros; destruct y; try (left; reflexivity); try (right; intros; discriminate).
    -
      destruct (sign_eq_dec s s0), (OrderedTypeEx.Nat_as_OT.eq_dec n n0);subst.
      + auto.
      + right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
    -
      destruct a, u.
      left.
      reflexivity.
    -
      destruct (Sym_t_as_MiniDecidableType.eq_dec t0 t1);
        unfold Sym_t_as_MiniDecidableType.eq in *; subst.
      + left; reflexivity.
      + right. intros H. inversion H. congruence.
    -
      destruct (Sym_t_as_MiniDecidableType.eq_dec t0 t1);
        unfold Sym_t_as_MiniDecidableType.eq in *; subst.
      + left; reflexivity.
      + right. intros H. inversion H. congruence.
    -
      (* TODO: this is not provavle with current induction principle! *)
      admit.
    -
      specialize (H y1).
      specialize (H0 y2).
      inversion H.
      +
        subst.
        inversion H0.
        *
          subst.
          left.
          reflexivity.
        *
          right.
          intros H3.
          inversion H3.
          congruence.
      +
        right.
        intros H3.
        inversion H3.
        auto.
    -
      specialize (H y).
      inversion H.
      +
        subst.
        left.
        reflexivity.
      +
        right.
        intros C.
        inversion C.
        congruence.
    -
      clear x.
      revert l0.
      induction H;intros.
      +
        destruct l0.
        * left. reflexivity.
        * right. congruence.
      +
        destruct l0.
        * right. congruence.
        * specialize (p t0).
          specialize (IHForall_type l0).
          f_equal.
          inversion p.
          --
            subst.
            inversion IHForall_type.
            ++
              inversion H0.
              subst.
              left.
              reflexivity.
            ++
              right.
              intros C.
              inversion C.
              subst.
              congruence.
          --
            right.
            intros C.
            inversion C.
            congruence.
    -
      specialize (H y).
      destruct H.
      + subst. left. reflexivity.
      +
        right.
        intros C.
        inversion C.
        congruence.
  Admitted.
  
End BasetTypes_t_as_MiniDecidableType.


Definition dt_info := Datatype.info unit.
Definition constr_info := Datatype.constr_info unit.
