(* include Stdlib.Option *)

type 'a m = 'a option

let map f = function
  | Some a -> Some (f a)
  | None -> None

let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false

let return (a: 'a): 'a m = Some a

let fail : 'a m = None

let bind (a: 'a m) (f: 'a -> 'b m) : 'b m = 
  match a with
  | Some a -> f a 
  | None -> None


let equal equality oa oa' = 
  match oa, oa' with
  | Some a, Some a' -> equality a a'
  | None, None -> true
  | _, _ -> false


let value (default : 'a) (oa : 'a option) =
  match oa with
  | Some a -> a
  | None -> default

let value_err (err : string) (oa : 'a option) =
  match oa with
  | Some a -> a
  | None -> Debug_ocaml.error err

let (let*) = bind

let pp ppf oa =
  let open Pp in
  match oa with
  | Some a -> !^"Some" ^^^ parens (ppf a)
  | None -> !^"None"


let to_list = function
  | Some a -> [a]
  | None -> []

let list (o_xs : ('a option) list) : 'a list = 
  List.filter_map (fun o -> o) o_xs


module ListM = struct

  let rec mapM f xs = 
    match xs with
    | [] -> return []
    | x :: xs ->
       let* y = f x in
       let* ys = mapM f xs in
       return (y :: ys)

end
