(** option type, following Haskell's Data.Option *)
type 'a t = 'a option

let return x = Some x

let bind x f = match x with
| None -> None
| Some x -> f x

let mzero = None

let map f = function
| None -> None
| Some x -> Some (f x)

let map_post x f = map f x

let get_default a = function
| None -> a
| Some a' -> a'