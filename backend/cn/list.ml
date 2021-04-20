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

let rec find_map f = function
  | [] -> None
  |  x :: xs -> match f x with
    | None -> find_map f xs
    | Some x -> Some x

let rec equal (equality : 'a -> 'a -> bool) (xs : 'a list) (xs' : 'a list) : bool = 
  match xs, xs' with
  | [], [] -> true
  | x::xs, x'::xs' -> equality x x' && equal equality xs xs'
  | _, _ -> false


let rec compare (comparison : 'a -> 'a -> int) (xs : 'a list) (xs' : 'a list) = 
  match xs, xs' with
  | [], [] -> 0
  | x::xs, x'::xs' -> 
     let compared = comparison x x' in
     if (compared = 0) then compare comparison xs xs' else compared
  | [], _ -> -1
  | _, [] -> 1

let assoc_opt (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v option = 
  match find_opt (fun (k',_) -> equality k k') l with
  | Some (_, v) -> Some v
  | None -> None

let assoc (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v = 
  snd (find (fun (k',_) -> equality k k') l )


let json jsonf list = 
  `List (map jsonf list)
