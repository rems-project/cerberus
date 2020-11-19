include Stdlib.List

let concat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    concat (map f xs)


let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs


let rec equal (equality : 'a -> 'a -> bool) (xs : 'a list) (xs' : 'a list) : bool = 
  match xs, xs' with
  | [], [] -> true
  | x::xs, x'::xs' -> equality x x' && equal equality xs xs'
  | _, _ -> false


let assoc_opt (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v option = 
  match find_opt (fun (k',_) -> equality k k') l with
  | Some (_, v) -> Some v
  | None -> None

let assoc (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v = 
  snd (find (fun (k',_) -> equality k k') l )
