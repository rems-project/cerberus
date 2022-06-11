open Pp

type item = {
    path : Ast.Terms.term; 
    it : IndexTerms.typed; 
    o_sct: Sctypes.t option;
  }

type t = item list


let pp_item {path; it; o_sct} = 
  Pp.parens (
      Ast.Terms.pp true path ^^ comma ^^ 
      IndexTerms.pp it ^^^ colon ^^^ 
      BaseTypes.pp (IndexTerms.bt it)
    )

let pp = Pp.list pp_item

let empty = []


type mapping = t
