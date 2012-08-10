(* Infer the comprehension variables for a set comprehension without explicitly
 * listed comprehension variables.  The first argument should return true for
 * variables that are currently bound in the enclosing environment (such
 * variables cannot become comprehension variables) *)
val setcomp_bindings : (Name.t -> bool) -> Ast.exp -> Set.Make(Name).t
