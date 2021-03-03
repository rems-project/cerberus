module Make (G : sig val global : Global.t end) = struct

  module L = Local.Make(G)
  open Global
  open IndexTerms

  let context = G.global.solver_context
  let solver = Z3.Solver.mk_simple_solver context

  let holds local (it : IndexTerms.t) = 
    let constraints = 
      SolverConstraintsNew.of_index_term G.global (not_ it) ::
      L.all_solver_constraints local
    in
    match Z3.Solver.check solver constraints with
    | Z3.Solver.UNSATISFIABLE -> true
    | Z3.Solver.SATISFIABLE -> false
    | Z3.Solver.UNKNOWN -> Debug_ocaml.error "SMT solver returned 'unknown'"

  let is_inconsistent local = holds local (bool_ false)

  let get_model () = Z3.Solver.get_model solver

  

end
