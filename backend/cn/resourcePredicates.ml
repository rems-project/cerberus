module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module StringMap = Map.Make(String)
module Loc = Locations
open Pp


type clause = {
    loc : Loc.t;
    guard : IT.t;
    packing_ft : LAT.packing_ft
  }

let pp_clause {loc; guard; packing_ft} =
  item "condition" (IT.pp guard) ^^ comma ^^^
  item "return type" (LAT.pp IT.pp packing_ft)

let subst_clause subst {loc; guard; packing_ft} =
  { loc = loc;
    guard = IT.subst subst guard;
    packing_ft = LAT.subst IT.subst subst packing_ft }


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



type definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oarg_bt : LS.t;
    clauses : (clause list) option;
  }





let pp_definition def =
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oarg_bt" (BT.pp def.oarg_bt) ^/^
  item "clauses" (match def.clauses with
                  | Some clauses -> Pp.list pp_clause clauses
                  | None -> !^"(uninterpreted)")


let instantiate_clauses def ptr_arg iargs = match def.clauses with
  | Some clauses ->
    let subst = IT.make_subst (
        (def.pointer, ptr_arg) ::
        List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs
      )
    in
    Some (List.map (subst_clause subst) clauses)
  | None -> None






let predicate_list struct_decls logical_pred_syms =
  []




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
          match provable (t_ clause.guard) with
          | `True -> Some clause
          | `False ->
            let loc = Loc.other __FUNCTION__ in
            match provable (t_ (not_ clause.guard loc)) with
            | `True -> try_clauses clauses
            | `False ->
              Pp.debug 5 (lazy (Pp.item "cannot prove or disprove clause guard"
                  (IT.pp clause.guard)));
              None
      in
      try_clauses clauses
