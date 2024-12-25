type t =
  | T of IndexTerms.t
  | Forall of (Sym.t * BaseTypes.t) * IndexTerms.t

val equal : t -> t -> bool

val compare : t -> t -> int

module Set : Set.S with type elt = t

val pp : t -> Pp.document

val json : t -> Yojson.Safe.t

val subst : [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> t -> t

val subst_ : (Sym.t * IndexTerms.t) list -> t -> t

val free_vars_bts : t -> BaseTypes.t Sym.Map.t

val free_vars : t -> Sym.Set.t

val alpha_equivalent : t -> t -> bool

val forall_ : Sym.t * BaseTypes.t -> IndexTerms.t -> t

val is_sym_lhs_equality : t -> (Sym.t * IndexTerms.t) option

val is_sym_equality : t -> (Sym.t * Sym.t) option

val is_equality : t -> ((IndexTerms.t * IndexTerms.t) * bool) option

val equates_to : IndexTerms.t -> t -> IndexTerms.t option

val dtree : t -> Cerb_frontend.Pp_ast.doc_tree

val is_forall : t -> bool

val is_interesting : t -> bool
