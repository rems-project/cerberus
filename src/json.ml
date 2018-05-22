type json =
    [ `Assoc of (string * json) list
    | `Bool of bool
    | `Float of float
    | `Floatlit of string
    | `Int of int
    | `Intlit of string
    | `List of json list
    | `Null
    | `String of string
    | `Stringlit of string
    | `Tuple of json list
    | `Variant of string * json option ]

let of_string s = `String s

let of_bool b = `Bool b

let of_int i = `Int i

let of_bigint n = `String (Nat_big_num.to_string n)

let of_option f = function
  | Some v -> f v
  | None -> `Null

let of_opt_string s = of_option of_string s

let of_list f xs = `List (List.map f xs)

let of_location l =
  let open Location_ocaml in
  let open Lexing in
  let of_pos p =
    `Assoc [("line", `Int (p.pos_lnum-1));
            ("ch", `Int (p.pos_cnum-p.pos_bol))]
  in match l with
  | Loc_unknown   -> `Null
  | Loc_other str -> `Null (* `String str *)
  | Loc_point p   -> of_pos p
  | Loc_region (p1, p2, _) -> `Assoc [("begin", of_pos p1); ("end", of_pos p2)]
