module IT = IndexTerms
module LAT = LogicalArgumentTypes

module Clause = struct
  type t =
    { loc : Locations.t;
      guard : IT.t;
      packing_ft : LAT.packing_ft
    }

  let pp { loc = _; guard; packing_ft } =
    let open Pp in
    item "condition" (IT.pp guard)
    ^^ comma
    ^^^ item "return type" (LAT.pp IT.pp packing_ft)


  let subst subst { loc; guard; packing_ft } =
    { loc;
      guard = IT.subst subst guard;
      packing_ft = LAT.subst IT.subst subst packing_ft
    }


  let lrt (pred_oarg : IT.t) clause_packing_ft =
    let module LRT = LogicalReturnTypes in
    let rec aux = function
      | LAT.Define (bound, info, lat) -> LRT.Define (bound, info, aux lat)
      | LAT.Resource (bound, info, lat) -> LRT.Resource (bound, info, aux lat)
      | LAT.Constraint (lc, info, lat) -> LRT.Constraint (lc, info, aux lat)
      | I output ->
        let loc = Locations.other __FUNCTION__ in
        let lc = LogicalConstraints.T (IT.eq_ (pred_oarg, output) loc) in
        LRT.Constraint (lc, (loc, None), LRT.I)
    in
    aux clause_packing_ft
end

module Definition = struct
  type t =
    { loc : Locations.t;
      pointer : Sym.t;
      iargs : (Sym.t * BaseTypes.t) list;
      oarg_bt : BaseTypes.t;
      clauses : Clause.t list option
    }

  let pp def =
    let open Pp in
    item "pointer" (Sym.pp def.pointer)
    ^/^ item "iargs" (Pp.list (fun (s, _) -> Sym.pp s) def.iargs)
    ^/^ item "oarg_bt" (BaseTypes.pp def.oarg_bt)
    ^/^ item
          "clauses"
          (match def.clauses with
           | Some clauses -> Pp.list Clause.pp clauses
           | None -> !^"(uninterpreted)")
end

let alloc =
  Definition.
    { loc = Locations.other (__FILE__ ^ ":" ^ string_of_int __LINE__);
      pointer = Sym.fresh_named "ptr";
      iargs = [];
      oarg_bt = Alloc.History.value_bt;
      clauses = None
    }


let instantiate_clauses (def : Definition.t) ptr_arg iargs =
  match def.clauses with
  | Some clauses ->
    let subst =
      IT.make_subst
        ((def.pointer, ptr_arg)
         :: List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs)
    in
    Some (List.map (Clause.subst subst) clauses)
  | None -> None


let identify_right_clause provable (def : Definition.t) pointer iargs =
  match instantiate_clauses def pointer iargs with
  | None ->
    (* "uninterpreted" predicates cannot be un/packed *)
    None
  | Some clauses ->
    let rec try_clauses : Clause.t list -> _ = function
      | [] -> None
      | clause :: clauses ->
        (match provable (LogicalConstraints.T clause.guard) with
         | `True -> Some clause
         | `False ->
           let loc = Locations.other __FUNCTION__ in
           (match provable (LogicalConstraints.T (IT.not_ clause.guard loc)) with
            | `True -> try_clauses clauses
            | `False ->
              Pp.debug
                5
                (lazy
                  (Pp.item "cannot prove or disprove clause guard" (IT.pp clause.guard)));
              None))
    in
    try_clauses clauses


(* determines if a resource predicate will be given to the solver
   TODO: right now this is an overapproximation *)
let given_to_solver (def : Definition.t) =
  match def.clauses with
  | None -> false
  | Some [] -> true
  | Some [ _ ] -> true
  | _ -> false


(*Extensibility hook. For now, all predicates are displayed as "interesting" in error reporting*)
let is_interesting : Definition.t -> bool = fun _ -> true
