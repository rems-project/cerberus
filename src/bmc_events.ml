open Bmc_analysis
open Core

open Cthread
open Z3

type action_id = int
type bmc_location = Expr.expr
type bmc_value = Expr.expr
type event_guard = Expr.expr

type bmc_action =
  | Read of action_id * thread_id * Cmm_csem.memory_order * bmc_location * bmc_value
  | Write of action_id * thread_id * Cmm_csem.memory_order * bmc_location * bmc_value 

type bmc_paction =
  | BmcAction of polarity * event_guard * bmc_action

let get_aid (action: bmc_action) = match action with
  | Read (aid, _, _, _, _)
  | Write (aid, _, _, _, _) ->
      aid

let get_thread (action: bmc_action) = match action with
  | Read (_, tid, _, _, _)
  | Write (_, tid, _, _, _) ->
      tid


let get_location (action: bmc_action) : bmc_value = match action with
  | Read (_, _, _, loc, _)
  | Write (_, _, _, loc, _) ->
      loc

let get_value (action: bmc_action) : bmc_value = match action with
  | Read (_, _, _, _, value)
  | Write (_, _, _, _, value) ->
      value

let aid_of_paction (BmcAction(_, _, a1)) : action_id = 
  get_aid a1

let value_of_paction (BmcAction(_, _, a1)) : bmc_value =
  get_value a1

let location_of_paction (BmcAction(_, _, a1)) : bmc_location =
  get_location a1

let guard_of_paction (BmcAction(_, guard, _)) : event_guard =
  guard

let thread_of_paction (BmcAction(_, _, a1)) : thread_id =
  get_thread a1


let paction_cmp (BmcAction(_, _, a1)) (BmcAction(_, _, a2)) =
  Pervasives.compare (get_aid a1) (get_aid a2)


type preexecution = {
  actions : bmc_paction Pset.set;

  initial_actions : bmc_paction Pset.set;

  sb : (action_id * action_id) Pset.set
}

let guard_actions (ctx: context)
                  (guard: event_guard)
                  (actions: bmc_paction Pset.set) : bmc_paction Pset.set =
  Pset.map paction_cmp (fun (BmcAction(pol, g, action)) ->
    BmcAction(pol, Boolean.mk_and ctx [guard; g], action)
  ) actions

let guard_preexec (ctx: context)
                  (guard: event_guard)
                  (preexec: preexecution) : preexecution =
  {preexec with actions = guard_actions ctx guard preexec.actions }

let string_of_memory_order = function
  | Cmm_csem.NA      -> "NA"
  | Cmm_csem.Seq_cst -> "seq_cst"
  | Cmm_csem.Relaxed -> "relaxed"
  | Cmm_csem.Release -> "release"
  | Cmm_csem.Acquire -> "acquire"
  | Cmm_csem.Consume -> "consume"
  | Cmm_csem.Acq_rel -> "acq_rel"

let string_of_action (action : bmc_action) = match action with
  | Read(aid, tid, memorder, loc, value) ->
      Printf.sprintf "%s(%d, %d, %s, %s, %s)"
            "Read" (aid) (tid)
            (string_of_memory_order memorder)
            (Expr.to_string loc)
            (Expr.to_string value)
  | Write(aid, tid, memorder, loc, value) ->
      Printf.sprintf "%s(%d, %d, %s, %s, %s)"
            "Write" (aid) (tid)
            (string_of_memory_order memorder)
            (Expr.to_string loc)
            (Expr.to_string value)

let string_of_paction (BmcAction(pol, guard, action): bmc_paction) = 
  match pol with
  | Pos -> 
      Printf.sprintf "BmcAction(%s, %s, %s)" "+" (string_of_action action) (Expr.to_string guard)
  | Neg ->
      Printf.sprintf "BmcAction(%s, %s, %s)" "-" (string_of_action action) (Expr.to_string guard)


let initial_preexec () = {
  actions = Pset.empty (paction_cmp);
  initial_actions = Pset.empty (paction_cmp);
  sb = Pset.empty (Pervasives.compare);
}

let add_initial_action (aid: action_id)
                       (action: bmc_paction)
                       (preexec : preexecution) : preexecution =
  {preexec with initial_actions = Pset.add action preexec.initial_actions;
  }


let add_action (aid : action_id) 
               (action : bmc_paction)
               (preexec : preexecution) : preexecution =
  {preexec with actions = Pset.add action preexec.actions;
  }


let print_preexec (preexec : preexecution) : unit =
  print_endline "ACTIONS";
  Pset.iter (fun v -> print_endline (string_of_paction v)) preexec.actions;
  print_endline "INITIAL_ACTIONS";
  Pset.iter (fun v -> print_endline (string_of_paction v)) preexec.initial_actions;
  print_endline "REL SB";
  Pset.iter (fun (a, b) -> Printf.printf "(%d, %d) " a b) preexec.sb;
  print_endline ""


let set_to_list (set : 'a Pset.set) f =
  Pset.fold (fun el l -> (f el) :: l) set []

let set_to_list_id (set: 'a Pset.set) =
  set_to_list set (fun x -> x)

(* TODO: switch to Pset.map since this allows type to be changed... *)  
let pos_cartesian_product (s1: (bmc_paction) Pset.set) 
                          (s2: (bmc_paction) Pset.set) 
                          : (action_id * action_id) Pset.set =
  Pset.fold (fun pa1 s_outer -> (
    match pa1 with
    | BmcAction(Pos, _, _) ->
      Pset.fold (fun pa2 s_inner ->
        Pset.add (aid_of_paction pa1, aid_of_paction pa2) s_inner)
        s2 (s_outer)
    | _ -> s_outer))
    s1 (Pset.empty Pervasives.compare)

let cartesian_product (s1: (bmc_paction) Pset.set) 
                      (s2: (bmc_paction) Pset.set) 
                      : (action_id * action_id) Pset.set =
  Pset.fold (fun pa1 s_outer -> (
    Pset.fold (fun pa2 s_inner ->
      Pset.add (aid_of_paction pa1, aid_of_paction pa2) s_inner)
      s2 (s_outer)
                      )) s1 (Pset.empty Pervasives.compare)

let merge_preexecs (p1 : preexecution) (p2: preexecution) : preexecution =
  { actions = Pset.union p1.actions p2.actions;
    initial_actions = Pset.union p1.initial_actions p2.initial_actions;
    sb = Pset.union p1.sb p2.sb}

