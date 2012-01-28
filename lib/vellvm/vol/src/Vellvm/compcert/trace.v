(***********************************************************)
(** trace and Trace                                        *)

Record Event : Set := mkEvent { }.

Inductive trace : Set :=
| trace_nil : trace
| trace_cons : Event -> trace -> trace
.

CoInductive Trace : Set :=
| Trace_cons : Event -> Trace -> Trace
.

Fixpoint trace_app (tr1 tr2:trace) : trace :=
match tr1 with
| trace_nil => tr2
| trace_cons e tr1' => trace_cons e (trace_app tr1' tr2)
end.

Fixpoint Trace_app (tr1:trace) (tr2:Trace) : Trace :=
match tr1 with
| trace_nil => tr2
| trace_cons e tr1' => Trace_cons e (Trace_app tr1' tr2)
end.

Lemma trace_app_nil__eq__trace : forall tr,
  trace_app tr trace_nil = tr.
Proof.
  induction tr; simpl; auto.
    rewrite IHtr. auto.
Qed.

Lemma nil_app_trace__eq__trace : forall tr,
  trace_app trace_nil tr = tr.
Proof. auto. Qed.

Lemma trace_app_commute : forall tr1 tr2 tr3,
  trace_app tr1 (trace_app tr2 tr3) = trace_app (trace_app tr1 tr2) tr3.
Proof.
  induction tr1; intros; simpl; auto.
    rewrite IHtr1. auto.
Qed.

Lemma nil_app_Trace__eq__Trace : forall tr,
  Trace_app trace_nil tr = tr.
Proof. auto. Qed.

Lemma Trace_app_commute : forall tr1 tr2 tr3,
  Trace_app tr1 (Trace_app tr2 tr3) = Trace_app (trace_app tr1 tr2) tr3.
Proof.
  induction tr1; intros; simpl; auto.
    rewrite IHtr1. auto.
Qed.

