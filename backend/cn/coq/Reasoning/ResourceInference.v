Require Import Coq.Lists.List.

From Cn Require Import Prooflog.

(** Inductive predicate which defines correctess of log inference step *)
Inductive log_entry_valid : log_entry -> Prop :=
| valid_resource_inference_step :
  forall ctx1 rtype ctx2,
  (* TODO: define validity conditions *)
  log_entry_valid (ResourceInferenceStep ctx1 rtype ctx2).

(** Proof log is valid if all entries are valid *)
Definition prooflog_valid (l:Prooflog.log) := List.Forall log_entry_valid l.

(* Automation to prove single entry *)
Ltac prove_log_entry_valid :=
  match goal with
  | [ |- log_entry_valid (ResourceInferenceStep _ _ _) ] =>
      (* TODO: define automation to prove validity *)
      constructor; try auto
  end.

Ltac prove_log_entry_list_valid :=
  match goal with
  | [ |- List.Forall log_entry_valid ?l ] =>
      let rec aux l :=
        match l with
        | nil => constructor
        | ?hd :: ?tl =>
            constructor; [ prove_log_entry_valid | aux tl ]
        end
      in aux l
  end.

(* Sample usage for the proof log extracted from CN:
Theorem resource_inference_steps_valid: prooflog_valid _cn_ResourceInferenceSteps.
Proof.
  unfold prooflog_valid.
  unfold _cn_ResourceInferenceSteps.
  prove_log_entry_list_valid.
Qed.
*)