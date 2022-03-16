type clause = {
    loc : Locations.t;
    guard : IndexTerms.t;
    packing_ft : ArgumentTypes.packing_ft
  }

val pp_clause : clause -> Pp.document
val subst_clause : IndexTerms.t Subst.t -> clause -> clause


type definition = {
    loc : Locations.t;
    pointer: Sym.t;
    iargs : (Sym.t * LogicalSorts.t) list;
    oargs : (string * LogicalSorts.t) list;
    clauses : clause list;
  }

val pp_definition : definition -> Pp.document


val predicate_list : Memory.struct_decls -> (string * definition) list
