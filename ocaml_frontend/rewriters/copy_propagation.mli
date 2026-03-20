(** Pure symbol rebinding elimination.

    Eliminates bindings of the form [let alias = pure(sym) in body]
    by substituting [sym] for [alias] throughout [body] and dropping
    the binding.  No memory events, sequencing, or values are changed.

    Also handles the extended case: if a binding has an effectful RHS
    whose tail expression is [pure(sym)], the binding is kept (for its
    side effects) but the pattern is changed to a wildcard and [alias]
    is substituted with [sym] in the body. *)

val transform_file : unit Core.file -> unit Core.file
