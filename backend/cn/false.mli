(* Module False - TODO: BCP: What is it?? *)

(* TODO: BCP: Should this be abstract? It's only used concretely in one place... *)
type t = False

val subst : 'a -> t -> t

val pp : t -> Pp.document

module SymSet : Set.S with type elt = Sym.t

val free_vars : t -> SymSet.t
