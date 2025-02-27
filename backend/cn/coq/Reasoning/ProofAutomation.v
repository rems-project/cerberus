From Ltac2 Require Import Ltac1 Ltac2 Notations Std Constr Env Ident.
 
From Cn Require Import Prooflog Request Resource Context.
Require Import Ltac2Utils ResourceInference.

(* Sample usage for the proof log extracted from CN:

Theorem resource_inference_steps_valid: prooflog_valid _cn_ResourceInferenceSteps.
Proof.
  unfold prooflog_valid.
  unfold _cn_ResourceInferenceSteps.
  ltac2:(prove_log_entry_list_valid ()).
Qed.

*)
 
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
       ResSet.Equal (ResSet.add (P upred, ?out) (set_from_list ?out_res)) (set_from_list ?in_res) /\ subsumed _ (Predicate.name upred) ] =>
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
         let p := predicate_of_request req in
         exists $p;
         Std.split false NoBindings;
         (* ResSet subset proof *)
         Control.focus 1 1 (fun () => ltac1:(subst;cbn;ResSetDecide.fsetdec));
         (* Second subgoal - subsumed *)
         Control.focus 1 1 (fun () => Std.constructor false; Std.reflexivity ())
     | _ =>
         Control.throw (Tactic_failure (Some (Message.of_string "Zero or more than one resource change between the input and output")))
     end
 end.
 
 Ltac2 prove_log_entry_valid () :=
   match! goal with
   | [ |- log_entry_valid (ResourceInferenceStep _ _ _) ] =>
       (* TODO: define automation to prove validity *)
       Std.constructor false;
       Control.focus 1 1 (fun () => Std.reflexivity ());
       Control.focus 1 1 (fun () => Std.reflexivity ());
       Control.focus 1 1 (fun () => Std.reflexivity ());
       Control.focus 1 1 (fun () => Std.reflexivity ());
       Control.focus 1 1 (fun () => 
       let clause := { on_hyps := None; on_concl := AllOccurrences } in
         Std.unfold [(const_to_const_reference constr:(@ctx_resources_set), AllOccurrences)] clause;
         Std.cbn 
           { rStrength := Std.Norm;
             rBeta := true;
             rMatch := true;
             rFix := true;
             rCofix := true;
             rZeta := true;
             rDelta := true;
             rConst := [const_to_const_reference  constr:(@set_from_list)]
           } clause ;
         res_set_remove_step ()
       )
   end.
 
 Ltac2 prove_log_entry_list_valid () :=
   match! goal with
   | [ |- List.Forall log_entry_valid ?l ] =>
       let rec aux l :=
         let nil_constr := constr:(@nil log_entry) in
         let cons_constr := constr:(@cons log_entry) in
         match Constr.Unsafe.kind l with
         | Constr.Unsafe.App f args =>
             let f_name := get_constructor_name f in
             let nil_name := get_constructor_name nil_constr in
             let cons_name := get_constructor_name cons_constr in
             if Constr.equal f_name nil_name then
               (* nil case *)
               Std.constructor false
             else if Constr.equal f_name cons_name then
               (* cons case *)
               let head := Array.get args 1 in
               let tail := Array.get args 2 in
               Std.constructor false;
               Control.focus 1 1 (fun () => prove_log_entry_valid ());
               Control.focus 1 1 (fun () => aux tail)
             else
               Control.throw (Tactic_failure (Some (Message.of_string "Not a list")))
         | _ =>
             Control.throw (Tactic_failure (Some (Message.of_string "Not a list")))
         end
       in aux l
   end.
 
 