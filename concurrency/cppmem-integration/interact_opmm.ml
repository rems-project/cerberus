(*========================================================================*)
(*                                                                        *)
(*             cppmem model exploration tool                              *)
(*                                                                        *)
(*                    Mark Batty                                          *)
(*                    Scott Owens                                         *)
(*                    Jean Pichon                                         *)
(*                    Susmit Sarkar                                       *)
(*                    Peter Sewell                                        *)
(*                                                                        *)
(*  This file is copyright 2011, 2012 by the above authors.               *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHE   *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

open Lem_pervasives
open Lem_relation
open Lem_set
open Lem_bool
open Lem_basic_classes
open Lem_tuple
open Lem_num
open Cmm
open Cmm_aux_ocaml
open MinimalOpsem 
open RelationalOpsem
open ExecutableOpsem
open Value
                        
let memory_order_tostring (mo:memory_order) : string = 
match mo with 
  | Cmm.NA      -> "na"
  | Cmm.Seq_cst -> "sc"
  | Cmm.Relaxed -> "rlx"
  | Cmm.Release -> "rel"
  | Cmm.Acquire -> "acq"
  | Cmm.Consume -> "con"
  | Cmm.Acq_rel -> "acq_rel"

let cst_tostring (c:Value.cst) : string = 
  match c with
  | Concrete i -> Printf.sprintf "%i" i
  | Symbolic s -> s

let value_tostring (v:Value.value) : string =
  match v with
  | Rigid c    -> cst_tostring c
  | Flexible f -> f

let tid_tostring (tid:tid) : string = 
  match tid with
  | Tid t -> let s = value_tostring t in
             if s = "thrd" then "thrd0" else s

let loc_tostring (loc:location) : string =
  match loc with
  | Loc l -> value_tostring l

let cvalue_tostring (cvalue:cvalue) : string = 
  match cvalue with
  | Cvalue c -> value_tostring c
  
let action_tostring (a:action) : string = 
  match a with
  | Load (aid, tid, mo, loc, value)  -> Printf.sprintf "%s a%s: Load_%s %s %s"
                                        (tid_tostring tid)
                                        aid 
                                        (memory_order_tostring mo) 
                                        (loc_tostring loc)
                                        (cvalue_tostring value)
  | Store (aid, tid, mo, loc, value) -> Printf.sprintf "%s a%s: Store_%s %s %s"
                                        (tid_tostring tid)
                                        aid 
                                        (memory_order_tostring mo) 
                                        (loc_tostring loc)
                                        (cvalue_tostring value)
  | _                                -> "?"

let action_pair_tostring (rel_name:string) ((a,b):action*action) : string =
  Printf.sprintf "a%s -> a%s" (aid_of a) (aid_of b)

let action_rel_tostring (rel_name:string) (r:(action*action) Pset.set) : string =
  String.concat ", " (List.map (action_pair_tostring rel_name)
                               (Pset.elements r))

let pre_ex_tostring (pre:pre_execution) : string =
  Printf.sprintf "%s\nsb: %s\nasw: %s"
   (String.concat ", " (List.map action_tostring (Pset.elements pre.actions)))
   (action_rel_tostring "sb" pre.sb)
   (action_rel_tostring "asw" pre.asw)

let step_tostring (step:exeStep) : string =
  match step with
  | ConcurrencyTau (a, s)    -> Printf.sprintf "%s" (action_tostring a)
  | ReadsFrom (c1, c2, a, s) -> Printf.sprintf "%s" (action_tostring a)

let is_terminated (step:exeStep) : bool =
  let state = stateOf step in
  List.length (Pset.elements (state.committed0)) = 
    List.length (Pset.elements (state.preEx.actions))

let rec exhaustive_aux (step:exeStep) (i:int) : unit =
  let next = Pset.elements (exeOpsemStep (stateOf step) standardEqualityCvalue) in
  print_string (String.make (2 * i) ' ');
  print_string (step_tostring step); 
  if is_terminated step then
     print_string " Terminated"
  else
    (if next = [] then print_string " Blocked");
  print_string "\n";
  List.iter (fun s -> exhaustive_aux s (i + 1)) next

let exhaustive (p:pre_execution) : unit =
  let initialSteps = Pset.elements (exeOpsemStep (initialExeState p) standardEqualityCvalue) in
  print_string (string_of_int (List.length initialSteps) ^ " initial step(s)\n");
  List.iter (fun s -> exhaustive_aux s 0) initialSteps

let run_opmm cilf =
  let exreses =
    List.rev
      (Eval.eval_file cilf
	 (fun exres exreses -> exres :: exreses)
	 []) in
  let pre_executions = 
    List.map 
      (fun e -> Iso.xo_of_exod (Executions.conv_execution_result e)) 
      exreses in
  print_string (string_of_int (List.length exreses) ^ " pre-execution(s)\n");

  List.iter (fun pre -> print_string (pre_ex_tostring pre); 
                        print_string "\n\n";
                        exhaustive pre; 
                        print_string "\n") 
            pre_executions



(*
let debug (p:pre_execution) : unit = 
  let a = List.find (fun a -> aid_of a = "0") (Pset.elements p.actions) in
  let eq = standardEqualityCvalue in
  let s = initialExeState p in
  let new_mo = List.hd (Pset.elements (addToMo a s)) in
  let new_wit = { s.exWitness0 with mo = new_mo; } in
  let new_committed = (Pset.add a s.committed0) in
  let new_ex = (s.preEx, new_wit, getRelations s.preEx new_wit) in 
  let is_cons = exIsConsistent_op_sym eq new_committed new_ex in
  let is_ext = execution_witness_equal(witnessRestrict new_wit s.committed0) s.exWitness0 in

  print_string (Printf.sprintf "#transitions: %i\n" (List.length (Pset.elements (exePerformStore s a eq))));
  print_string (Printf.sprintf "is_sc: %b\n" (is_seq_cst a));
  print_string (Printf.sprintf "is_atomic: %b\n" (is_at_atomic_location p.lk a));
  print_string (Printf.sprintf "is_consistent: %b\n" is_cons);
  print_string (Printf.sprintf "is_extension: %b\n" is_ext);

  print_string (Printf.sprintf "assumptions: %b\n" (assumptions new_ex ));
  print_string (Printf.sprintf "det_read_op: %b\n" (det_read_op new_committed new_ex ));
  print_string (Printf.sprintf "coherent_memory_use: %b\n" (coherent_memory_use new_ex ));
  print_string (Printf.sprintf "consistent_atomic_rf: %b\n" (consistent_atomic_rf new_ex ));
  print_string (Printf.sprintf "consistent_hb: %b\n" (consistent_hb new_ex ));
  print_string (Printf.sprintf "consistent_mo_op: %b\n" (consistent_mo_op new_committed new_ex ));
  print_string (Printf.sprintf "consistent_non_atomic_rf: %b\n" (consistent_non_atomic_rf new_ex ));
  print_string (Printf.sprintf "locks_only_consistent_lo_op: %b\n" (locks_only_consistent_lo_op new_committed new_ex ));
  print_string (Printf.sprintf "locks_only_consistent_locks_op: %b\n" (locks_only_consistent_locks_op new_committed new_ex ));
  print_string (Printf.sprintf "rmw_atomicity_op: %b\n" (rmw_atomicity_op new_committed new_ex ));
  print_string (Printf.sprintf "sc_accesses_consistent_sc_op: %b\n" (sc_accesses_consistent_sc_op new_committed new_ex ));
  print_string (Printf.sprintf "sc_accesses_sc_reads_restricted: %b\n" (sc_accesses_sc_reads_restricted new_ex ));
  print_string (Printf.sprintf "sc_fenced_sc_fences_heeded: %b\n" (sc_fenced_sc_fences_heeded new_ex ));
  print_string (Printf.sprintf "tot_empty: %b\n" (tot_empty new_ex ));
  print_string (Printf.sprintf "well_formed_rf_op_sym: %b\n" (well_formed_rf_op_sym eq new_committed new_ex ));
  print_string (Printf.sprintf "well_formed_threads: %b\n" (well_formed_threads new_ex ));

(*
print_string (Printf.sprintf "well_formed_action: %b\n" ( (Pset.for_all  (fun a -> well_formed_action a) p.actions) ));    
print_string (Printf.sprintf "actions_respect_location_kinds: %b\n" ( actions_respect_location_kinds p.actions p.lk ));    
print_string (Printf.sprintf "blocking_observed: %b\n" ( blocking_observed p.actions p.sb ));    
print_string (Printf.sprintf "inj_on aid: %b\n" ( inj_on instance_Basic_classes_Eq_Cmm_action_dict instance_Basic_classes_Eq_string_dict aid_of p.actions ));    
print_string (Printf.sprintf "relation sb: %b\n" ( relation_over instance_Basic_classes_SetType_Cmm_action_dict p.actions p.sb ));    
print_string (Printf.sprintf "relation asw: %b\n" ( relation_over instance_Basic_classes_SetType_Cmm_action_dict p.actions p.asw ));    
print_string (Printf.sprintf "threadwise sb: %b\n" ( threadwise p.actions p.sb ));    
print_string (Printf.sprintf "interthread asw: %b\n" ( interthread p.actions p.asw ));    
print_string (Printf.sprintf "isStrictPartialOrder sb: %b\n" ( isStrictPartialOrder   instance_Basic_classes_SetType_Cmm_action_dict instance_Basic_classes_Eq_Cmm_action_dict p.sb ));    
print_string (Printf.sprintf "isStrictPartialOrder dd: %b\n" ( isStrictPartialOrder   instance_Basic_classes_SetType_Cmm_action_dict instance_Basic_classes_Eq_Cmm_action_dict p.dd )); 
print_string (Printf.sprintf "dd in sb: %b\n" ( Pset.subset    p.dd p.sb ));    
print_string (Printf.sprintf "indeterminate_sequencing: %b\n" ( indeterminate_sequencing p ));    
print_string (Printf.sprintf "isIrreflexive sbasw: %b\n" ( isIrreflexive instance_Basic_classes_SetType_Cmm_action_dict instance_Basic_classes_Eq_Cmm_action_dict (sbasw p) ));    
print_string (Printf.sprintf "finite_prefixes: %b\n" ( finite_prefixes instance_Basic_classes_SetType_Cmm_action_dict instance_Basic_classes_Eq_Cmm_action_dict (sbasw p) p.actions ));
print_string (Printf.sprintf "disjoint_allocs: %b\n" ( disjoint_allocs p.actions ));
print_string (Printf.sprintf "relOver sb: %b\n" ( relOver instance_Basic_classes_SetType_Cmm_action_dict p.sb p.actions ));
*)

 (* let relDefinedOn = Pset.(union)(relDomain 
  dict_Basic_classes_SetType_a dict_Basic_classes_SetType_a r) (relRange dict_Basic_classes_SetType_a dict_Basic_classes_SetType_a r) in *)

 let sb = Pset.elements p.sb in
 let relDefinedOn = List.append (List.map snd sb) (List.map fst sb) in
 let actions = Pset.elements p.actions in

 print_string (Printf.sprintf "sb[0] = actions[0]: %b\n" (List.hd relDefinedOn = List.hd actions));
 print_string (Printf.sprintf "sb[1] = actions[1]: %b\n" (List.hd (List.tl relDefinedOn) = List.hd (List.tl actions)));

 print_string  (String.concat ", " (List.map action_tostring actions));
 print_string  "\n";
 print_string  (String.concat ", " (List.map action_tostring relDefinedOn))

*)

