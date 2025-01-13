module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module StringMap = Map.Make (String)
module Loc = Locations
open Pp

type clause =
  { loc : Loc.t;
    guard : IT.t;
    packing_ft : LAT.packing_ft
  }

let pp_clause { loc = _; guard; packing_ft } =
  item "condition" (IT.pp guard) ^^ comma ^^^ item "return type" (LAT.pp IT.pp packing_ft)


let subst_clause subst { loc; guard; packing_ft } =
  { loc; guard = IT.subst subst guard; packing_ft = LAT.subst IT.subst subst packing_ft }


let clause_lrt (pred_oarg : IT.t) clause_packing_ft =
  let rec aux = function
    | LAT.Define (bound, info, lat) -> LRT.Define (bound, info, aux lat)
    | LAT.Resource (bound, info, lat) -> LRT.Resource (bound, info, aux lat)
    | LAT.Constraint (lc, info, lat) -> LRT.Constraint (lc, info, aux lat)
    | I output ->
      let loc = Loc.other __FUNCTION__ in
      let lc = LC.t_ (IT.eq_ (pred_oarg, output) loc) in
      LRT.Constraint (lc, (loc, None), LRT.I)
  in
  aux clause_packing_ft


type definition =
  { loc : Loc.t;
    pointer : Sym.t;
    iargs : (Sym.t * LS.t) list;
    oarg_bt : LS.t;
    clauses : clause list option
  }

let alloc =
  { loc = Locations.other (__FILE__ ^ ":" ^ string_of_int __LINE__);
    pointer = Sym.fresh_named "ptr";
    iargs = [];
    oarg_bt = Alloc.History.value_bt;
    clauses = None
  }


let pp_definition def =
  item "pointer" (Sym.pp def.pointer)
  ^/^ item "iargs" (Pp.list (fun (s, _) -> Sym.pp s) def.iargs)
  ^/^ item "oarg_bt" (BT.pp def.oarg_bt)
  ^/^ item
        "clauses"
        (match def.clauses with
         | Some clauses -> Pp.list pp_clause clauses
         | None -> !^"(uninterpreted)")


let instantiate_clauses def ptr_arg iargs =
  match def.clauses with
  | Some clauses ->
    let subst =
      IT.make_subst
        ((def.pointer, ptr_arg)
         :: List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs)
    in
    Some (List.map (subst_clause subst) clauses)
  | None -> None


open IndexTerms
open LogicalConstraints

let identify_right_clause provable def pointer iargs =
  match instantiate_clauses def pointer iargs with
  | None ->
    (* "uninterpreted" predicates cannot be un/packed *)
    None
  | Some clauses ->
    let rec try_clauses = function
      | [] -> None
      | clause :: clauses ->
        (match provable (t_ clause.guard) with
         | `True -> Some clause
         | `False ->
           let loc = Loc.other __FUNCTION__ in
           (match provable (t_ (not_ clause.guard loc)) with
            | `True -> try_clauses clauses
            | `False ->
              Pp.debug
                5
                (lazy
                  (Pp.item "cannot prove or disprove clause guard" (IT.pp clause.guard)));
              None))
    in
    try_clauses clauses

let rec explicit_negative_guards_aux (cs : clause list) (prev_negated : IT.t ) : clause list =
  let cerb_loc = Cerb_location.unknown in
  match cs with
  | [] -> []
  | {loc; guard=cur_guard; packing_ft} :: cs' ->
      let cur = {loc; guard=IT.and_ [prev_negated; cur_guard] cerb_loc; packing_ft} in
      let so_far_ng = IT.and_ [IT.not_ cur_guard cerb_loc; prev_negated] cerb_loc in
      cur :: explicit_negative_guards_aux cs' so_far_ng

let explicit_negative_guards (cs : clause list) : clause list =
  let cerb_loc = Cerb_location.unknown in
  match cs with
  | [] -> []
  | h :: tl -> h :: explicit_negative_guards_aux tl (IT.not_ h.guard cerb_loc)

  (*type definition =
  { loc : Loc.t;
    pointer : Sym.t;
    iargs : (Sym.t * LS.t) list;
    oarg_bt : LS.t;
    clauses : clause list option
  }*)

(*  let alpha_unique ss =
  let rec f ss = function
    | Resource ((name, (re, bt)), info, t) ->
      let t2 = f (SymSet.add name ss) t in
      let name2, t3 = suitably_alpha_rename ss name t2 in
      Resource ((name2, (re, bt)), info, t3)
    | Define ((name, it), info, t) ->
      let t2 = f (SymSet.add name ss) t in
      let name, t3 = suitably_alpha_rename ss name t2 in
      Define ((name, it), info, t3)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I -> I
  in
  f ss*)
open Option
(*
  let rec subst_definition (substitution : _ Subst.t) = function
    | {loc; pointer; iargs; oarg_bt; clauses=o_clauses} ->
      let new_clauses =
        let@ clauses = o_clauses in
        Some (List.map (subst_clause substitution) clauses) (* TODO: independent? *)
      in

    match lrt with
    | Define ((name, it), info, t) ->
      let it = IT.subst substitution it in
      let name, t = suitably_alpha_rename substitution.relevant name t in
      Define ((name, it), info, subst substitution t)
    | Resource ((name, (re, bt)), info, t) ->
      let re = RT.subst substitution re in
      let name, t = suitably_alpha_rename substitution.relevant name t in
      let t = subst substitution t in
      Resource ((name, (re, bt)), info, t)
    | Constraint (lc, info, t) ->
      let lc = LogicalConstraints.subst substitution lc in
      let t = subst substitution t in
      Constraint (lc, info, t)
    | I -> I


  and alpha_rename_ ~from ~to_ t =
    ( to_,
      if Sym.equal from to_ then
        t
      else
        subst (IT.make_rename ~from ~to_) t )


  and alpha_rename from t =
    let to_ = Sym.fresh_same from in
    alpha_rename_ ~from ~to_ t


  and suitably_alpha_rename syms s t =
    if SymSet.mem s syms then
      alpha_rename s t
    else
      (s, t)


  let rec bound = function
    | Define ((s, _), _, lrt) -> SymSet.add s (bound lrt)
    | Resource ((s, _), _, lrt) -> SymSet.add s (bound lrt)
    | Constraint (_, _, lrt) -> bound lrt
    | I -> SymSet.empty


  let alpha_unique ss =
    let rec f ss = function
      | Resource ((name, (re, bt)), info, t) ->
        let t = f (SymSet.add name ss) t in
        let name, t = suitably_alpha_rename ss name t in
        Resource ((name, (re, bt)), info, t)
      | Define ((name, it), info, t) ->
        let t = f (SymSet.add name ss) t in
        let name, t = suitably_alpha_rename ss name t in
        Define ((name, it), info, t)
      | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
      | I -> I
    in
    f ss *)


(* determines if a resource predicate will be given to the solver
   TODO: right now this is an overapproximation *)
let given_to_solver def =
  match def.clauses with
  | None -> false
  | Some [] -> true
  | Some [ _ ] -> true
  | _ -> false


(*Extensibility hook. For now, all predicates are displayed as "interesting" in error reporting*)
let is_interesting : definition -> bool = fun _ -> true
