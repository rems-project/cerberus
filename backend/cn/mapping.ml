open Pp

type item = {
    path : Ast.Terms.path; 
    it : IndexTerms.typed; 
  }

type t = item list


let pp_item {path; it} = 
  Pp.parens (
      Ast.Terms.pp_path true path ^^ comma ^^ 
      IndexTerms.pp it
    )

let pp = Pp.list pp_item

let empty = []


type mapping = t
