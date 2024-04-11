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


let rec compare (comparison : 'a -> 'a -> int) (xs : 'a list) (xs' : 'a list) =
  match xs, xs' with
  | [], [] -> 0
  | x::xs, x'::xs' ->
     let compared = comparison x x' in
     if (compared = 0) then compare comparison xs xs' else compared
  | [], _ -> -1
  | _, [] -> 1


let mem equality y xs =
  let rec aux = function
    | [] -> false
    | x :: xs -> equality y x || aux xs
  in
  aux xs


let assoc_opt (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v option =
  match find_opt (fun (k',_) -> equality k k') l with
  | Some (_, v) -> Some v
  | None -> None

let assoc (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : 'v =
  snd (find (fun (k',_) -> equality k k') l )

let mem_assoc (equality : 'k -> 'k -> bool) (k : 'k) (l : ('k * 'v) list) : bool =
  match assoc_opt equality k l with
  | Some _ -> true
  | None -> false


let json jsonf list =
  `List (map jsonf list)





let map_split (f : 'a -> 'b * 'c) (xs : 'a list) : 'b list * 'c list =
  fold_right (fun x (ys, zs) ->
      let (y, z) = f x in
      (y :: ys, z :: zs)
    ) xs ([], [])



let map_fst (f : 'a -> 'c) (xs : ('a * 'b) list) : ('c * 'b) list =
  map (fun (a, b) -> (f a, b)) xs

let map_snd (f : 'b -> 'c) (xs : ('a * 'b) list) : ('a * 'c) list =
  map (fun (a, b) -> (a, f b)) xs


let rec separate_and_group (by : 'b -> 'a option) : 'b list -> ('a option * 'b list) list =
  function
  | [] -> []
  | b :: bs -> 
    match by b, separate_and_group by bs with
    | Some a, ((None, bs') :: abs) -> 
        (Some a, bs') :: abs
    | Some a, abs ->
        (Some a, []) :: abs
    | None, ((None, bs') :: abs) ->
        (None, b :: bs') :: abs
    | None, abs ->
        (None, [b]) :: abs


let empty = function
  | [] -> true
  | _ -> false

let non_empty l = not (empty l)

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: tl -> last tl
