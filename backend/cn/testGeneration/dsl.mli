module IT = IndexTerms
module CF = Cerb_frontend

type gen =
  | Arbitrary of CF.Ctype.ctype
  | Return of CF.Ctype.ctype * IT.t
  | Filter of Sym.sym * CF.Ctype.ctype * IT.t * gen
  | Map of Sym.sym * CF.Ctype.ctype * IT.t * gen
  | Alloc of CF.Ctype.ctype * Sym.sym
  | Struct of CF.Ctype.ctype * (string * Sym.sym) list

val string_of_gen : gen -> string

type gen_context = (Sym.sym * gen) list

val pp_gen_context : gen_context -> Pp.document

val optimize : gen_context -> gen_context

val compile : Constraints.goal -> gen_context
