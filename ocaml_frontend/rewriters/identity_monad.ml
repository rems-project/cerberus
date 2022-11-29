type 'a t = 'a
let return = fun z -> z
let bind m f = f m
let (>>=) = bind
let mapM = List.map
let foldlM f xs init =
  List.fold_left (fun acc x ->
    f x acc
  ) init xs

let unwrap (x: 'a t) : 'a = x
