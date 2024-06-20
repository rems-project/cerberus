(* This file re-exports the standard List library functions together
   with a bunch of other useful list utilities. *)
(* TODO: BCP: Probably not worth bothering with an mli file for this one... *)

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

(* NOTE: this exists in Stdlib since 5.1 *)
let is_empty = function
  | [] -> true
  | _ -> false

let non_empty l = not (is_empty l)

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: tl -> last tl

let rec sorted_and_unique compare = function
  | [] | [_] -> true
  | x :: (y :: _ as tl) ->
    match compare x y with
    | -1 -> sorted_and_unique compare tl
    | _ -> false

(* NOTE: this exists in Stdlib since 5.1 *)
let find_index pred xs =
  let rec aux idx = function
    | [] -> None
    | x::xs -> if pred x then Some idx else aux (idx+1) xs in
  aux 0 xs
