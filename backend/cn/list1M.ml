open Resultat
open List1

let mapM (f : 'a -> ('b, 'e) m) (list : 'a list1) : ('b list1, 'e) m =
  let (hd, tl) = List1.dest list in
  let* hd' = f hd in
  let* tl' = ListM.mapM f tl in
  return (make (hd', tl'))




