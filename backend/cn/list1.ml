(* non-empty lists *)

type 'a list1 = 'a * 'a list
type 'a t = 'a list1

let dest (hd, tl) = (hd, tl)
let make (hd, tl) = (hd, tl)

let to_list (hd, tl) = List.cons hd tl

let head (hd, _) = hd
let tail (_, tl) = tl

let cons (a : 'a) (l : 'a list1) = 
  let (hd, tl) = l in
  (a, hd :: tl)

let one a = (a, [])

let map (f : 'a -> 'b) (l : 'a list1) : 'b list1 =
  let (hd, tl) = l in
  (f hd, List.map f tl)


let concat (l1 : 'a list1) (l2 : 'a list1) : 'a list1 = 
  let (hd1,tl1) = l1 in
  (hd1, tl1 @ to_list l2)

let (@) = concat


let equal equality l1 l2 = 
  List.equal equality (to_list l1) (to_list l2)


let length (hd, tl) = 1 + List.length tl


let combine (hd, tl) (hd', tl') = 
  make ((hd, hd'), List.combine tl tl')
