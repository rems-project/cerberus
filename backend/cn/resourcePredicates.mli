type clause = {
    loc : Locations.t;
    guard : IndexTerms.t;
    packing_ft : LogicalArgumentTypes.packing_ft
  }

val pp_clause : clause -> Pp.document
val subst_clause : IndexTerms.t Subst.t -> clause -> clause


type definition = {
    loc : Locations.t;
    pointer: Sym.t;
    iargs : (Sym.t * LogicalSorts.t) list;
    oargs : (Sym.t * LogicalSorts.t) list;
    clauses : (clause list) option;
  }

val pp_definition : definition -> Pp.document


val predicate_list : Memory.struct_decls -> Sym.t list -> (Sym.t * definition) list
