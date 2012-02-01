(* t is the type of globally unique identifier paths to definitions *)
type t
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val from_id : Ident.t -> t
(*
val get_name : t -> Name.t
 *)
val mk_path : Name.t list -> Name.t -> t
val numpath : t
val listpath : t
val boolpath : t
val setpath : t
val stringpath : t
val unitpath : t
val get_name : t -> Name.t
val check_prefix : Name.t -> t -> bool
val to_ident : t -> Ident.t
val to_name : t -> Name.t
(*
val to_rope : (Ast.lex_skips -> BatRope.t) -> BatRope.t -> t -> BatRope.t
val get_lskip: t -> Ast.lex_skips
val add_pre_lskip : Ast.lex_skips -> t -> t
val drop_parens : t -> t
val is_lower : t -> bool
val is_upper : t -> bool
val to_lower : t -> t
val to_upper : t -> t
val prefix_is_lower : t -> bool
val prefix_is_upper : t -> bool
val prefix_to_lower : t -> t
val prefix_to_upper : t -> t
 *)
