module Make(C : sig include Types.Global_defs val consts : Typed_ast.NameSet.t end) : sig
  (* For each target, returns the (pre-backend) transformation function, and the
  * local variable renaming function (for Typed_ast.Exp_context.avoid) *)
  val get_transformation : 
    Typed_ast.target option -> 
    ((Typed_ast.env -> Typed_ast.checked_module -> (Typed_ast.env * Typed_ast.checked_module)) *
     ((Name.t -> bool) * (Ulib.Text.t -> (Name.t -> bool) -> Name.t)))
end
