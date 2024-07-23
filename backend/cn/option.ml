include Stdlib.Option

type 'a m = 'a option

let map f = function Some a -> Some (f a) | None -> None

let map_fst f = function Some (a, b) -> Some (f a, b) | None -> None

let map_snd f = function Some (a, b) -> Some (a, f b) | None -> None

let is_some = function Some _ -> true | None -> false

let is_none = function None -> true | Some _ -> false

let get = Stdlib.Option.get

let return (a : 'a) : 'a m = Some a

let fail : 'a m = None

let bind (a : 'a m) (f : 'a -> 'b m) : 'b m = match a with Some a -> f a | None -> None

let equal equality oa oa' =
  match (oa, oa') with
  | Some a, Some a' -> equality a a'
  | None, None -> true
  | _, _ -> false


(* let value (default : 'a) (oa : 'a option) = *)
(*   match oa with *)
(*   | Some a -> a *)
(*   | None -> default *)

let value_err (err : string) (oa : 'a option) =
  match oa with Some a -> a | None -> Cerb_debug.error err


let ( let@ ) = bind

let pp ppf oa =
  let open Pp in
  match oa with Some a -> !^"Some" ^^^ parens (ppf a) | None -> !^"None"


let json jsonf oa = match oa with Some a -> jsonf a | None -> `Null

let to_list = function Some a -> [ a ] | None -> []

module ListM = struct
  let rec mapM f xs =
    match xs with
    | [] -> return []
    | x :: xs ->
      let@ y = f x in
      let@ ys = mapM f xs in
      return (y :: ys)
end
