Require Import Orders Equalities.
Require Import MSets.

Inductive integerBaseType : Set :=  (*r standard signed integer types (\S6.2.5\#4) *)
 | IChar : integerBaseType (*r corresponds to \textbf{signed/unsigned char} *)
 | Short : integerBaseType (*r corresponds to \textbf{short int} *)
 | Int : integerBaseType
 | Long : integerBaseType (*r corresponds to \textbf{long int} *)
 | LongLong : integerBaseType (*r corresponds to \textbf{long long int} *).

Inductive integerType : Set :=  (*r integer types (\S6.2.5\#17) *)
 | Bool : integerType (*r corresponds to \textbf{\_Bool} *)
 | Signed : integerBaseType -> integerType
 | Unsigned : integerBaseType -> integerType.

Inductive qualifier : Set :=  (*r type qualifiers (\S6.7.3) *)
 | Const : qualifier
 | Restrict : qualifier
 | Volatile : qualifier.

Inductive basicType : Set :=  (*r basic types (\S6.2.5\#14) *)
 | Char : basicType
 | Integer : integerType -> basicType.

Module OrderedQualifier.
  Definition t := qualifier.

  Definition eq := @eq t.
  Instance eq_equiv : Equivalence eq.

  Definition lt a b :=
    match a, b with
    | Const, Const => False
    | Restrict, Restrict => False
    | Volatile, Volatile => False
    | Const, Restrict => True
    | Const, Volatile => True
    | Restrict, Const => False
    | Restrict, Volatile => True
    | Volatile, Const => False
    | Volatile, Restrict => False
    end.

  Instance lt_irreflexive : Irreflexive lt.
  Proof.
    unfold Irreflexive.
    unfold Reflexive.
    unfold complement.
    intros x.
    case x; now simpl.
  Qed.

  Instance lt_transitive : Transitive lt.
  Proof.
    unfold Transitive.
    intros x y z.
    case x; case y; case z; now simpl.
  Qed.

  Instance lt_strorder : StrictOrder lt.

  Definition compare (a b : t) :=
    match a, b with
    | Const, Const => Eq
    | Restrict, Restrict => Eq
    | Volatile, Volatile => Eq
    | Const, Restrict => Lt
    | Const, Volatile => Lt
    | Restrict, Const => Gt
    | Restrict, Volatile => Lt
    | Volatile, Const => Gt
    | Volatile, Restrict => Gt
    end.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    unfold eq.
    split; now subst.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros.
    case_eq (compare x y); unfold compare; constructor.
      unfold eq.
      case_eq x; case_eq y; intros; subst; simpl; (now auto || discriminate).

      unfold lt.
      case_eq x; case_eq y; intros; subst; simpl; (now auto || discriminate).      

      unfold lt.
      case_eq x; case_eq y; intros; subst; simpl; (now auto || discriminate).      
  Qed.

  Lemma eq_dec x y : {eq x y}+{~eq x y}.
  Proof.
    unfold eq; case_eq x; case_eq y; intros _ _; auto; right; discriminate.
  Qed.

  Definition eq_leibniz (a b : t) (H : eq a b) := H.
End OrderedQualifier.

Module QualifierSet := MakeWithLeibniz OrderedQualifier.

Definition qualifiers : Set := QualifierSet.t.

Inductive type : Set :=  (*r $\texttt{Ail}_\tau$ types *)
 | Void : qualifiers -> type (*r \texttt{void} type (\S6.2.5\#19) *)
 | Basic : qualifiers -> basicType -> type (*r basic types (\S6.2.5\#14) *)
 | Array : type -> nat -> type (*r array types (\S6.2.5\#20) *)
 | Function : type -> list type -> type (*r function types *)
 | Pointer : qualifiers -> type -> type (*r pointer types *).

Inductive storageDuration : Set :=  (*r storage duration (\S6.2.4\#1) *)
 | Static : storageDuration
 | Thread : storageDuration
 | Automatic : storageDuration
 | Allocated : storageDuration.

Inductive typeCategory := 
 | LvalueT : type -> typeCategory
 | ExpressionT : type -> typeCategory.

(** induction principles *)
Section type_rect.

Variables
  (P_list_type : list type -> Prop)
  (P_type : type -> Prop).

Hypothesis
  (H_Void : forall qualifiers, P_type (Void qualifiers))
  (H_Basic : forall qualifiers basicType, P_type (Basic qualifiers basicType))
  (H_Array : forall ty, P_type ty -> forall n, P_type (Array ty n))
  (H_Function : forall ty_list, P_list_type ty_list -> forall ty, P_type ty -> P_type (Function ty ty_list))
  (H_Pointer : forall qualifiers ty, P_type ty -> P_type (Pointer qualifiers ty))
  (H_list_type_nil : P_list_type nil)
  (H_list_type_cons : forall ty, P_type ty -> forall ty_list, P_list_type ty_list -> P_list_type (cons ty ty_list)).

Fixpoint type_ott_ind ty : P_type ty :=
  match ty as x return P_type x with
  | Void qs => H_Void qs
  | Basic qs bt => H_Basic qs bt
  | Array t s => H_Array t (type_ott_ind t) s
  | Function t t_list =>
      H_Function t_list
        ( (fix type_list_ott_ind t_l : P_list_type t_l :=
            match t_l as x return P_list_type x with
            | nil => H_list_type_nil
            | cons t' t_list' => H_list_type_cons t' (type_ott_ind t') t_list' (type_list_ott_ind t_list')
            end) t_list)
        t (type_ott_ind t)
  | (Pointer qs t) => H_Pointer qs t (type_ott_ind t)
end.

End type_rect.
