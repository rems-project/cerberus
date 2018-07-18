open Bmc_utils
open Core
open Printf
open Z3

type aid = int
type tid = int

type z3_location = Expr.expr
type z3_value    = Expr.expr
type guard       = Expr.expr

type memory_order = Cmm_csem.memory_order

type action =
  | Load  of aid * tid * memory_order * z3_location * z3_value
  | Store of aid * tid * memory_order * z3_location * z3_value
  | RMW   of aid * tid * memory_order * z3_location * z3_value * z3_value
  | Fence of aid * tid * memory_order

type bmc_action =
  | BmcAction of polarity * guard * action

let aid_of_action (a: action) = match a with
  | Load  (aid, _, _, _, _)
  | Store (aid, _, _, _, _)
  | RMW   (aid, _, _, _, _, _)
  | Fence (aid, _, _) ->
      aid

let wval_of_action (a: action) = match a with
  | Store (_, _, _, _, v) -> v
  | _ -> assert false

let get_action (BmcAction(_, _, action): bmc_action) =
  action

let bmc_action_cmp (BmcAction(_, _, a1)) (BmcAction(_, _, a2)) =
  compare (aid_of_action a1) (aid_of_action a2)

(* ===== PREEXECS ===== *)

type preexec = {
  actions         : bmc_action list;
  initial_actions : bmc_action list;
}

let mk_initial_preexec : preexec =
  { actions         = []
  ; initial_actions = []
  }

let add_action action (preexec: preexec) : preexec =
  {preexec with actions = action::preexec.actions}

let add_initial_action action (preexec: preexec) : preexec =
  {preexec with initial_actions = action::preexec.initial_actions}

let guard_action (guard: Expr.expr) (BmcAction(pol, g, action): bmc_action) =
  BmcAction(pol, mk_implies guard g, action)

let guard_preexec (guard: Expr.expr) (preexec: preexec) =
  {preexec with actions = List.map (guard_action guard) preexec.actions}

let combine_preexecs (preexecs: preexec list) =
  List.fold_left (fun acc preexec ->
    { actions         = preexec.actions @ acc.actions
    ; initial_actions = preexec.initial_actions @ acc.initial_actions
    }) mk_initial_preexec preexecs

(* ===== PPRINTERS ===== *)
let string_of_memory_order = function
  | Cmm_csem.NA      -> "NA"
  | Cmm_csem.Seq_cst -> "seq_cst"
  | Cmm_csem.Relaxed -> "relaxed"
  | Cmm_csem.Release -> "release"
  | Cmm_csem.Acquire -> "acquire"
  | Cmm_csem.Consume -> "consume"
  | Cmm_csem.Acq_rel -> "acq_rel"

let string_of_polarity = function
  | Pos -> "+"
  | Neg -> "-"

let pp_action (a: action) =
  match a with
  | Load(aid,tid,memorder,loc,rval) ->
      sprintf "Load(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string rval)
  | Store(aid, tid, memorder,loc,wval) ->
      sprintf "Store(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string wval)
  | _ -> assert false

let pp_bmcaction (BmcAction(pol, guard, action): bmc_action) =
  sprintf "Action(%s,%s,%s)"
          (*(string_of_polarity pol)*) ""
          (*(Expr.to_string guard)*)   ""
          (pp_action action)

let pp_preexec (preexec: preexec) =
  sprintf ">>Initial:\n%s\n>>Actions:\n%s\n"
          (String.concat "\n" (List.map pp_bmcaction preexec.initial_actions))
          (String.concat "\n" (List.map pp_bmcaction preexec.actions))
