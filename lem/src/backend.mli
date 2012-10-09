(* The various backends that generate text from typed asts *)
module Make(C : sig val avoid : Typed_ast.var_avoid_f end) : sig
  val ident_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val hol_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val ocaml_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val isa_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val isa_header_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val coq_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val tex_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val tex_inc_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t * Ulib.Text.t
  val html_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
end
