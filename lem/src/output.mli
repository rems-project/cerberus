type t

type t' =
  | Kwd' of string
  | Ident' of BatRope.t
  | Num' of int

type id_annot =  (* kind annotation for latex'd identifiers *)
  | Term_const
  | Term_ctor
  | Term_field 
  | Term_method 
  | Term_var 
  | Term_var_toplevel
  | Term_spec 
  | Type_ctor
  | Type_var
  | Module_name
  | Class_name
  | Target

val emp : t
val kwd : string -> t
val id : id_annot -> BatRope.t -> t
val num : int -> t
val ws : Ast.lex_skips -> t
val str : BatRope.t -> t
val err : string -> t
val meta : string -> t
val texspace :  t
val (^) : t -> t -> t
val flat : t list -> t
val concat : t -> t list -> t
val to_rope : BatRope.t -> (Ast.lex_skip -> BatRope.t) -> (t' -> t' -> bool) -> t -> BatRope.t
val to_rope_option_tex : (Ast.lex_skip -> BatRope.t) -> (t' -> t' -> bool) -> bool -> t -> BatRope.t option
val to_rope_ident : id_annot ->  BatRope.t -> BatRope.t
val to_rope_single : t -> BatRope.t

val tex_escape : BatRope.t -> BatRope.t

val tex_command_escape : BatRope.t -> BatRope.t
val tex_command_label  : BatRope.t -> BatRope.t
val tex_command_name  : BatRope.t -> BatRope.t

val ml_comment_to_rope : Ast.ml_comment -> BatRope.t
