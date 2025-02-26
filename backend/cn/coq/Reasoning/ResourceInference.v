Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetInterface.

From Cn Require Import Prooflog Request Resource Context.


(* Helper functoin to get set of resources from contex *)

Definition ctx_resources_set (l:((list (Resource.t * Z)) * Z)) : Resource.ResSet.t
  :=
  Resource.set_from_list (List.map fst (fst l)).

(** Inductive predicate which defines correctess of log inference step *)
Inductive log_entry_valid : log_entry -> Prop :=

(* simple case: non-recursive request, no packing *)

| simple_resource_inference_step:
  forall iname  ipointer  iargs
    oname  opointer  oargs
    err out lines oloc
    icomputational ilogical iresources iconstraints iglobal
    ocomputational ological oresources oconstraints oglobal,

  (* The following parts of context are not changed *)
  icomputational = ocomputational ->
  iglobal = oglobal ->
  ilogical = ological ->
  iconstraints = oconstraints ->

  let in_res := ctx_resources_set iresources in
  let out_res := ctx_resources_set oresources in

  (* alt. definition sketch:
  let res_diff := Resource.ResSet.diff in_res out_res in
  Resource.ResSet.cardinal res_diff = 1 /\
  ...
   *)

  (* [out_res] is a subset of [in_res] with exactly one element [used] removed. *)
  (exists (upred: Request.Predicate.t),
      Resource.ResSet.remove (P upred, out) in_res = out_res /\
      Request.subsumed iname upred.(Request.Predicate.name)
  )
  ->

    log_entry_valid
      (ResourceInferenceStep
         (* input context *)
         {|
           Context.computational := icomputational;
           Context.logical := ilogical;
           Context.resources := iresources;
           Context.constraints := iconstraints;
           Context.global := iglobal
         |}

         (* request type *)
         (PredicateRequest
            err (* unused *)
            (* input predicate *)
            {| Predicate.name:=iname; Predicate.pointer:=ipointer; Predicate.iargs:=iargs |}
            oloc (* unused *)
            ((
                (* output predicate *)
                {| Predicate.name:=oname; Predicate.pointer:=opointer; Predicate.iargs:=oargs |},
                  out
              ), lines (* unused *)
         ))

         (* output context *)
         {|
           Context.computational := ocomputational;
           Context.logical := ological;
           Context.resources := oresources;
           Context.constraints := oconstraints;
           Context.global := oglobal
         |}
      ).

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

 (* Experimental Ltac2 automation below *)
From Ltac2 Require Import Ltac2 Notations Std Constr.
Require Import Reasoning.Ltac2Utils.

Ltac2 predicate_of_request (t : constr) :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
    let r_constr := constr:(@Request.P) in
    let r_constr_name := get_constructor_name r_constr in
    let f_name := get_constructor_name f in
    if Constr.equal f_name r_constr_name then
      if Int.equal (Array.length args) 1 then
        Array.get args 0 
      else
        Control.throw (Tactic_failure (Some (Message.of_string "Term is not a fully applied P")))
    else
      Control.throw (Tactic_failure (Some (Message.of_string "Term is not a P")))
| _ =>
    Control.throw (Tactic_failure (Some (Message.of_string "Term is not an application (and thus not a P)")))
end.

Ltac2 res_set_remove_step () :=
match! goal with
| [ |- exists upred,
      ResSet.remove (P upred, ?out) (set_from_list ?in_res) = set_from_list ?out_res /\ subsumed _ (Predicate.name upred) ] =>
    (* break down goal into components *)
    let outname   := Fresh.in_goal @out in
    let inresname := Fresh.in_goal @in_res in
    let outresname:= Fresh.in_goal @out_res in
    let clause := { on_hyps := None; on_concl := AllOccurrences } in
    Std.remember false (Some inresname) (fun _ => in_res) None clause;
    Std.remember false (Some outresname) (fun _ => out_res) None clause;
    Std.remember false (Some outname) (fun _ => out) None clause;
    (* now try to compare lists *)
    let list_of_constr l := destruct_list (constr:(Resource.t)) l in
    let in_res_list  := list_of_constr  in_res in
    let out_res_list := list_of_constr out_res in
    let diff := const_list_subtract in_res_list out_res_list in
    match diff with
    | [res] =>
        (* single resource [res] matched, extract request as [req] *)
        let (req,out') := destruct_pair res in
        (* debug *)
        (* Message.print (Message.of_constr req); *)
        let p := predicate_of_request req in
        exists $p
    | _ =>
        Control.throw (Tactic_failure (Some (Message.of_string "Zero or more than one resource change between the input and output")))
    end
end.
