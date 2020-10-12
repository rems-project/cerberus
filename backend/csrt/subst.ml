open Pp

type ('a,'b) t = { before: 'a; after: 'b }

let pp app bpp {before; after} = 
  parens (!^"substitute" ^^^ app before ^^^ !^"with" ^^^ bpp after)


let make_substs
      (substitution_function : ('a,'b) t -> 'c -> 'c)
      (substs : (('a,'b) t) list)
      (c : 'c) : 'c 
  =
  List.fold_left (fun c substitution -> substitution_function substitution c)
    c substs


