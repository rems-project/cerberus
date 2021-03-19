module Make (G : sig val global : Global.t end) = struct

  module L = Local.Make(G)
  open IndexTerms

  let context = SolverConstraints.context
  let solver = Z3.Solver.mk_simple_solver context

  let check local (expr : Z3.Expr.expr) = 
    let () = Debug_ocaml.begin_csv_timing "solver" in
    let constraints = 
      Z3.Boolean.mk_not context expr ::
      L.all_solver_constraints local
    in
    let result = 
      try Z3.Solver.check solver constraints with
      | Z3.Error err -> 
         Debug_ocaml.error ("Z3 error: " ^ err)
    in
    let () = Debug_ocaml.end_csv_timing () in
    match result with
    | Z3.Solver.UNSATISFIABLE -> true
    | Z3.Solver.SATISFIABLE -> false
    | Z3.Solver.UNKNOWN -> Debug_ocaml.error "SMT solver returned 'unknown'"

  let holds local it = 
    check local (SolverConstraints.of_index_term G.global it)

  let holds_forall local quantifiers body = 
    let expr = 
      List.fold_right (fun (sym,bt) expr ->
          let q = SolverConstraints.of_index_term G.global 
                    (sym_ (bt, sym))
          in    
          let q = Z3.Quantifier.mk_forall_const context [q] 
                    expr None [] [] None None 
          in
          Z3.Quantifier.expr_of_quantifier q
        ) quantifiers (SolverConstraints.of_index_term G.global body)
    in
    check local expr


  let is_inconsistent local = holds local (bool_ false)

  let get_model () = Z3.Solver.get_model solver

  

end
