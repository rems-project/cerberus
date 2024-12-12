type output = O of IndexTerms.t [@@unboxed]

val pp_output : output -> Pp.document

type predicate = Request.Predicate.t * output

type qpredicate = Request.QPredicate.t * output

type t = Request.t * output

val pp : Request.t * output -> Pp.document

val json : Request.t * output -> Yojson.Safe.t

val subst : [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> t -> t

val free_vars : t -> Sym.Set.t

val derived_lc1 : t -> IndexTerms.t list

val derived_lc2 : t -> t -> IndexTerms.t list

val disable_resource_derived_constraints : bool ref

val pointer_facts : new_resource:t -> old_resources:t list -> IndexTerms.t list
