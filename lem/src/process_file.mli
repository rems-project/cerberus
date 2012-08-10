open Typed_ast

val print_msg : Ast.l -> string -> string -> unit

val parse_file : string -> Ast.defs * Ast.lex_skips

type instances = Types.instance list Types.Pfmap.t

val check_ast_as_module : 
  Targetset.t ->
  Name.t list ->
  (Types.type_defs * instances) * env ->
  Ulib.Text.t ->
  Ast.defs * Ast.lex_skips ->
  (Types.type_defs * instances * instances) * env *
  (def list * Ast.lex_skips)

val check_ast : 
  Targetset.t ->
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
  Ulib.Text.t list ref ->               (* alldoc accumulator *)
  Ulib.Text.t list ref ->               (* alldoc-inc accumulator *)
  Ulib.Text.t list ref ->               (* alldoc-use_inc accumulator *)
  unit

val output_alldoc : string -> string -> Ulib.Text.t list ref -> Ulib.Text.t list ref -> Ulib.Text.t list ref -> unit
