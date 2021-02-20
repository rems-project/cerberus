(* copying bits and pieces from https://github.com/alastairreid/asl-interpreter/blob/master/libASL/tcheck.ml and 
https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)
(* and the bmc backend *)


open Global
module LC = LogicalConstraints



let initial_context =
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","true");
      ("unsat_core", "true");
    ] 


module Make (G : sig val global : Global.t end) = struct

  module L = Local.Make(G)

  let z3_wrapper z3_work = 
    try Lazy.force z3_work with
    | Z3.Error (msg : string) -> 
       Debug_ocaml.error ("Z3 error:" ^ msg)



  let ctxt = G.global.solver_context
  let solver = Z3.Solver.mk_simple_solver ctxt


  let array_select_after_sym = Z3.Symbol.mk_string ctxt "array_select_after"
  let array_index_shift_right_sym = Z3.Symbol.mk_string ctxt "array_index_shift_right_sym"

  let array_select_after_sym = 
    Z3.FuncDecl.mk_func_decl ctxt array_select_after_sym
      []

  let get_model () = Z3.Solver.get_model solver


  let constraint_holds local constr = 
    let constrs = 
      SolverConstraints.of_index_term G.global (LC.unpack (LC.negate constr)) ::
      L.all_solver_constraints local 
    in
    match z3_wrapper (lazy (Z3.Solver.check solver constrs)) with
    | UNSATISFIABLE -> true
    | SATISFIABLE -> false
    | UNKNOWN -> 
       let open Pp in
       print stderr !^"internal error: constraint solver returned 'Unknown'";
       print stderr (item "reason" (!^(Z3.Solver.get_reason_unknown solver)));
       print stderr (item "lc" (LC.pp constr));
       print stderr (item "checked" (flow_map (break 1) string (List.map Z3.Expr.to_string constrs)));
       Debug_ocaml.error "constraint solver returned 'Unknown'"


  let is_inconsistent local =
    constraint_holds local (LC (Bool false))


  let equal local it1 it2 =
    constraint_holds local (LC.LC (IndexTerms.EQ (it1, it2)))

  let ge local it1 it2 =
    constraint_holds local (LC.LC (IndexTerms.GE (it1, it2)))

  let gt local it1 it2 =
    constraint_holds local (LC.LC (IndexTerms.GT (it1, it2)))

  let le local it1 it2 =
    constraint_holds local (LC.LC (IndexTerms.LE (it1, it2)))

  let lt local it1 it2 =
    constraint_holds local (LC.LC (IndexTerms.LT (it1, it2)))

  let is_global local it = 
    List.exists (fun (s, LS.Base bt) ->
      equal local it (S (bt, s))
    ) G.global.logical


  let resource_for_pointer local it
       : (Sym.t * RE.t) option = 
    let points = 
      List.filter_map (fun (name, re) ->
          match RE.pointer re with
          | Some pointer when equal local it pointer ->
             Some (name, re) 
          | _ ->
             None
        ) (L.all_named_resources local)
    in
    match points with
    | [] -> None
    | [r] -> Some r
    | _ -> Debug_ocaml.error ("multiple resources found: " ^ (Pp.plain (Pp.list RE.pp (List.map snd points))))

  let resource_around_pointer local it
       : (Sym.t * RE.t) option = 
    let points = 
      List.filter_map (fun (name, re) ->
          match RE.footprint re with
          | Some (pointer,size) when 
                 constraint_holds local 
                   (LC.LC (IT.And [IT.LocLE (pointer, it);
                                   IT.LocLT (it, Offset (pointer, size));
                      ])) ->
             Some (name, re) 
          | _ ->
             None
        ) (L.all_named_resources local)
    in
    match points with
    | [] -> None
    | [r] -> Some r
    | _ -> Debug_ocaml.error ("multiple resources found: " ^ (Pp.plain (Pp.list RE.pp (List.map snd points))))


  let predicate_for local id iargs
       : (Sym.t * RE.predicate) option = 
    let open Resources in
    let preds = 
      List.filter_map (fun (name, re) ->
          match re with
          | Predicate pred when predicate_name_equal pred.name id ->
             let its = 
               List.map (fun (iarg, iarg') ->
                     (IndexTerms.EQ (iarg, iarg'))
                 ) (List.combine iargs pred.iargs)
             in
             if constraint_holds local (LC.LC (IndexTerms.And its))
             then Some (name, pred) 
             else None
          | _ ->
             None
        ) (L.all_named_resources local)
    in
    match preds with
    | [] -> None
    | [r] -> Some r
    | _ -> 
       let resources = List.map (fun (_, pred) -> Predicate pred) preds in
       Debug_ocaml.error ("multiple resources found: " ^ (Pp.plain (Pp.list RE.pp resources)))



  let used_resource_for_pointer local it : (Locations.t list) option = 
    let points = 
      List.filter_map (fun (name, (re, where)) ->
          match RE.pointer re with
          | Some pointer when equal local it pointer -> Some where
          | _ -> None
        ) (L.all_named_used_resources local)
    in
    match points with
    | [] -> None
    | r :: _ -> Some r



  let used_resource_around_pointer local it
       : (Locations.t list) option = 
    let points = 
      List.filter_map (fun (name, (re, where)) ->
          match RE.footprint re with
          | Some (pointer,size) when 
                 constraint_holds local 
                   (LC.LC (IT.And [IT.LocLE (pointer, it);
                                   IT.LocLT (it, Offset (pointer, size));
                      ])) ->
             Some where 
          | _ ->
             None
        ) (L.all_named_used_resources local)
    in
    match points with
    | [] -> None
    | r :: _ -> Some r


end
