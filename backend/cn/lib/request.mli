type init =
  | Init
  | Uninit

val pp_init : init -> Pp.document

type name =
  | Owned of Sctypes.t * init
  | PName of Sym.t
[@@deriving eq]

val pp_name : name -> Pp.document

val dtree_of_name : name -> Cerb_frontend.Pp_ast.doc_tree

val subsumed : name -> name -> bool

module Predicate : sig
  type t =
    { name : name;
      pointer : IndexTerms.t;
      iargs : IndexTerms.t list
    }

  val alloc : name

  val subst : [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> t -> t

  val dtree : t -> Cerb_frontend.Pp_ast.doc_tree
end

val make_alloc : IndexTerms.t -> Predicate.t

module QPredicate : sig
  type t =
    { name : name;
      pointer : IndexTerms.t;
      q : Sym.t * BaseTypes.t;
      q_loc : Locations.t;
      step : IndexTerms.t;
      permission : IndexTerms.t;
      iargs : IndexTerms.t list
    }

  val alpha_rename_ : Sym.t -> t -> t

  val alpha_rename : t -> t

  val subst : [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> t -> t

  val dtree : t -> Cerb_frontend.Pp_ast.doc_tree

  val get_lower_bound : t -> IndexTerms.t

  val get_upper_bound : t -> IndexTerms.t

  val get_bounds : t -> IndexTerms.t * IndexTerms.t
end

type t =
  | P of Predicate.t
  | Q of QPredicate.t

val equal : t -> t -> bool

val compare : t -> t -> int

val get_name : t -> name

val same_name : t -> t -> bool

val pp_aux : t -> 'a Terms.annot option -> Pp.document

val pp : t -> Pp.document

val json : t -> Yojson.Safe.t

val subst : [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> t -> t

val free_vars_bts : t -> IndexTerms.BT.t Sym.Map.t

val free_vars : t -> Sym.Set.t

val alpha_equivalent : t -> t -> bool

val steps_constant : t -> bool

val dtree : t -> Cerb_frontend.Pp_ast.doc_tree

val get_iargs : t -> IndexTerms.t list

val get_pointer : t -> IndexTerms.t
