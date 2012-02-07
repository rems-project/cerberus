open Typed_ast

val print_msg : Ast.l -> string -> string -> unit

val parse_file : string -> Ast.defs * Ast.lex_skips

type instances = Types.instance list Types.Pfmap.t

val check_ast_as_module : 
  Name.t list ->
  (Types.type_defs * instances) * env ->
  BatRope.t ->
  Ast.defs * Ast.lex_skips ->
  (Types.type_defs * instances * instances) * env *
  (def list * Ast.lex_skips)

val check_ast : 
  Name.t list ->
  (Types.type_defs * instances) * env ->
  Ast.defs * Ast.lex_skips ->
  (Types.type_defs * instances * instances) * env *
  (def list * Ast.lex_skips)

val output : 
  string ->                           (* The path to the library *)
  target option ->                    (* Backend name (None for the identity backend) *) 
  Typed_ast.var_avoid_f ->
  (Types.type_defs * instances) -> (* The full environment built after all typechecking, and transforming *)
  checked_module list ->              (* The typechecked modules *)
  BatRope.t list ref ->               (* TODO: find out what this is for ??? *)
  BatRope.t list ref ->               (* TODO: find out what this is for ??? *)
  unit

val output_alldoc : string -> string -> BatRope.t list ref -> BatRope.t list ref -> unit
