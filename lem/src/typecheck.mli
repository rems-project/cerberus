open Types

val check_defs : 
  Name.t list ->
  type_defs * instance list Pfmap.t ->
  Typed_ast.env ->
  Ast.defs ->
  (* The second instance is just the new instances *)
  (type_defs * instance list Pfmap.t * instance list Pfmap.t) * Typed_ast.env * Typed_ast.def list

