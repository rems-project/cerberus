type ('a,'b) t = { s: 'a; swith: 'b }


let make_substs
      (substitution_function : ('a,'b) t -> 'c -> 'c)
      (substs : (('a,'b) t) list)
      (c : 'c) : 'c 
  =
  List.fold_left (fun c substitution -> substitution_function substitution c)
    c substs
