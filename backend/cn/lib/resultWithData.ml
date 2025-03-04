type ('a, 'b) result_with_data =
  | Yes of 'a
  | No of 'b
  | Unknown of 'b
  | Error of 'b

type ('a, 'b) m = ('a, 'b) result_with_data

let return x = Yes x

let bind (a : ('a, 'b) m) (f : 'a -> ('c, 'b) m) : ('c, 'b) m =
  match a with Yes x -> f x | No e -> No e | Unknown e -> Unknown e | Error e -> Error e


let ( let@ ) = bind

let pp_result_with_data pp_a pp_b r =
  let open Pp in
  match r with
  | Yes x -> !^"Yes: " ^/^ pp_a x
  | No e -> !^"No: " ^/^ pp_b e
  | Unknown e -> !^"Unknown: " ^/^ pp_b e
  | Error e -> !^"Error: " ^/^ pp_b e


let is_no r = match r with No _ -> true | _ -> false

let is_yes r = match r with Yes _ -> true | _ -> false

let is_unknown r = match r with Unknown _ -> true | _ -> false

let is_error r = match r with Error _ -> true | _ -> false

let map f r =
  match r with
  | Yes x -> Yes (f x)
  | No e -> No e
  | Unknown e -> Unknown e
  | Error e -> Error e


let equal eq_a eq_b r r' =
  match (r, r') with
  | Yes a, Yes a' -> eq_a a a'
  | No e, No e' -> eq_b e e'
  | Unknown e, Unknown e' -> eq_b e e'
  | Error e, Error e' -> eq_b e e'
  | _, _ -> false


  (* Gives a single canonical result *)
  let combine_results (e : 'b) (results : ('a, 'b) result_with_data list) : ('a, 'b) result_with_data =
    match results with
    | [] -> Error e
    | h :: t ->
      let combine acc res =
        match (acc, res) with
        | Yes l, _ -> Yes l
        | _, Yes l -> Yes l
        | Error s, _ -> Error s
        | _, Error s -> Error s
        | Unknown s, _ -> Unknown s
        | _, Unknown s -> Unknown s
        | No s, _ -> No s
      in
      List.fold_left combine h t