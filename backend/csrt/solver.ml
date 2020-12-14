(* copying bits and pieces from https://github.com/alastairreid/asl-interpreter/blob/master/libASL/tcheck.ml and 
https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)
(* and the bmc backend *)


open Global
module LC = LogicalConstraints



let initial_context =
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","true")
    ] 


module Make (G : sig val global : Global.t end) = struct

  module L = Local.Make(G)

  let logfile = "/tmp/z3.log"

  let handle_z3_problems todo =
    if not (Z3.Log.open_ logfile) then 
      Debug_ocaml.error ("Z3 logfile: could not open " ^ logfile)
    else 
      try let result = todo () in Z3.Log.close (); result with
      | Z3.Error (msg : string) -> 
         Z3.Log.close ();
         Debug_ocaml.error ("Z3 error:" ^ msg)


  let constraint_holds local lc = 
    let ctxt = G.global.solver_context in
    let solver = Z3.Solver.mk_simple_solver ctxt in
    let sc = SolverConstraints.of_index_term G.global (LC.unpack (LC.negate lc)) in
    let lcs = sc :: L.all_solver_constraints local in
    (* let () = debug_typecheck_lcs lcs (local, global) in *)
    let checked = 
      handle_z3_problems (fun () -> 
          Z3.Solver.add solver lcs; Z3.Solver.check solver []
        )
    in
    match checked with
    | UNSATISFIABLE -> (true,solver)
    | SATISFIABLE -> (false,solver)
    | UNKNOWN -> (false,solver)



  let is_consistent local =
    let (unreachable,_) = constraint_holds local (LC (Bool false)) in
    (not unreachable)


  let equal local it1 it2 =
    let c = LC.LC (IndexTerms.EQ (it1, it2)) in
    let (holds,_) = constraint_holds local c in
    holds

  let ge local it1 it2 =
    let c = LC.LC (IndexTerms.GE (it1, it2)) in
    let (holds,_) = constraint_holds local c in
    holds

  let lt local it1 it2 =
    let c = LC.LC (IndexTerms.LT (it1, it2)) in
    let (holds,_) = constraint_holds local c in
    holds


  let resource_for local it
       : (Sym.t * RE.t) option = 
    let points = 
      List.filter_map (fun (name, re) ->
          let holds = equal local it (RE.key re) in
          (if holds then Some (name, re) else None)
        ) (L.all_named_resources local)
    in
    match points with
    | [] -> None
    | [r] -> Some r
    | _ -> Debug_ocaml.error ("multiple resources found: " ^ (Pp.plain (Pp.list RE.pp (List.map snd points))))


  let used_resource_for local it
      : (Loc.t list) option = 
    let points = 
      List.filter_map (fun (name, (re, where)) ->
          let holds = equal local it (RE.key re) in
          (if holds then Some (where) else None)
        ) (L.all_named_used_resources local)
    in
    match points with
    | [] -> None
    | r :: _ -> Some r


end
