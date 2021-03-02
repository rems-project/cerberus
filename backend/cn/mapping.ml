open Pp

type item = {
    path : Path.t; 
    sym : Sym.t; 
    bt : BaseTypes.t
  }

type t = item list


let pp_item {path; sym; bt} = 
  Pp.parens (
      Path.pp path ^^ comma ^^ 
      Sym.pp sym ^^ comma ^^ 
      BaseTypes.pp bt
    )

let pp = Pp.list pp_item

let empty = []


type mapping = t
