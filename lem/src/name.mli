(* t is the type of plain names, either normal or infix, e.g., x or cmp or ++ *)
type t
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val from_rope : BatRope.t -> t
val to_rope : t -> BatRope.t
val to_rope_tex : Output.id_annot -> t -> BatRope.t
(*val to_rope_core : Output.id_annot -> Ast.v -> BatRope.t*)
val fresh : BatRope.t -> (t -> bool) -> t
val fresh_list : int -> BatRope.t -> (t -> bool) -> t list
val rename : (BatRope.t -> BatRope.t) -> t -> t
val starts_with_upper_letter : t -> bool
val starts_with_lower_letter : t -> bool
val capitalize : t -> t
val uncapitalize : t -> t

(* lskips_t is the type of names with immediately preceding spaces, comments and
* newlines, as well as surrounding `` and (), e.g., (* Foo *) x or (++) or `y` *)
type lskips_t
val lskip_pp : Format.formatter -> lskips_t -> unit
val from_x : Ast.x_l -> lskips_t
val from_ix : Ast.ix_l -> lskips_t
val add_lskip : t -> lskips_t
val strip_lskip : lskips_t -> t
val to_output : Output.id_annot -> lskips_t -> Output.t
val to_output_quoted : Output.id_annot -> lskips_t -> Output.t
val add_pre_lskip : Ast.lex_skips -> lskips_t -> lskips_t
val get_lskip : lskips_t -> Ast.lex_skips
val drop_parens : lskips_t -> lskips_t
val add_parens : lskips_t -> lskips_t
val lskip_rename : (BatRope.t -> BatRope.t) -> lskips_t -> lskips_t
val replace_lskip : lskips_t -> Ast.lex_skips -> lskips_t
val get_prec : (Precedence.op -> Precedence.t) -> lskips_t -> Precedence.t
