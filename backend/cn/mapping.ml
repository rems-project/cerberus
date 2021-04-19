open Pp

type item = {
    path : Path.t; 
    it : IndexTerms.t; 
  }

type t = item list


let pp_item {path; it} = 
  Pp.parens (
      Path.pp path ^^ comma ^^ 
      IndexTerms.pp it
    )

let pp = Pp.list pp_item

let empty = []


type mapping = t
