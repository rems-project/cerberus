open Global
module LC = LogicalConstraints




let logfile = "/tmp/z3.log"


let initial_context =
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","true")
    ] 


(*** running Z3 **************************************************************)


let handle_z3_problems todo =
  if not (Z3.Log.open_ logfile) then 
    Debug_ocaml.error ("Z3 logfile: could not open " ^ logfile)
  else 
    try let result = todo () in Z3.Log.close (); result with
    | Z3.Error (msg : string) -> 
       Z3.Log.close ();
       Debug_ocaml.error ("Z3 error:" ^ msg)


(* let debug_typecheck_lcs lcs (local, global) =
 *   if !Debug_ocaml.debug_level > 0 then () else
 *     List.iter (fun lc -> 
 *         match WellTyped.WLC.welltyped (loc: Loc.t) (local, global) lc with
 *         | Ok () -> ()
 *         | Error _ -> Debug_ocaml.error "illtyped logical constraint"
 *       ) lcs *)





  


let constraint_holds (local, global) lc = 
  let ctxt = global.solver_context in
  Debug_ocaml.begin_csv_timing "constraint_holds";
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let sc = SolverConstraints.of_index_term global (LC.unpack (LC.negate lc)) in
  let lcs = sc :: Local.all_solver_constraints local in
  (* let () = debug_typecheck_lcs lcs (local, global) in *)
  let checked = 
    handle_z3_problems
      (fun () ->
        Z3.Solver.add solver lcs;
        (* Debug_ocaml.end_csv_timing (); *)
        Debug_ocaml.begin_csv_timing "Z3.Solver.check";
        let result = Z3.Solver.check solver [] in
        Debug_ocaml.end_csv_timing ();
        result
      )
  in
  Debug_ocaml.end_csv_timing ();
  match checked with
  | UNSATISFIABLE -> (true,ctxt,solver)
  | SATISFIABLE -> (false,ctxt,solver)
  | UNKNOWN -> (false,ctxt,solver)









let is_consistent (local, global) =
  let (unreachable,_,_) = 
    constraint_holds (local, global) (LC (Bool false)) in
  (not unreachable)


let equal (local, global) it1 it2 =
  let c = LC.LC (IndexTerms.EQ (it1, it2)) in
  let (holds,_,_) = constraint_holds (local, global) c in
  holds


let resource_for_pointer (local, global) pointer_it
     : (Sym.t * RE.t) option = 
  let points = 
    List.filter_map (fun (name, re) ->
        let holds = equal (local, global) pointer_it (RE.pointer re) in
        (if holds then Some (name, re) else None)
      ) (Local.all_named_resources local)
  in
  Tools.at_most_one "multiple points-to for same pointer" points


let used_resource_for_pointer (local, global) pointer_it
    : (Loc.t list) option = 
  let points = 
    List.filter_map (fun (name, (re, where)) ->
        let holds = equal (local, global) pointer_it (RE.pointer re) in
        (if holds then Some (where) else None)
      ) (Local.all_named_used_resources local)
  in
  match points with
  | [] -> None
  | r :: _ -> Some r
