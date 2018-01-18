type t =
  | Int of int
  | Str of string
  | Array of t list
  | Map of (string * t) list

let in_quotes s =
  let escaped_no_unicode s =
    String.escaped s
      (* TODO: this is a horrible hack *)
    |> Str.global_replace (Str.regexp "\\\\[0-9]+") ""
  in
  "\"" ^ (escaped_no_unicode s) ^ "\""

let rec in_commas f = function
  | []    -> ""
  | [x]   -> f x
  | x::xs -> f x ^ ", " ^ in_commas f xs

let rec string_of = function
  | Int   i  -> string_of_int i
  | Str   s  -> in_quotes s
  | Array vs -> "[" ^ in_commas string_of vs ^ "]"
  | Map   vs ->
    "{" ^ in_commas (fun (k,v) -> in_quotes k ^ ":" ^ string_of v) vs ^ "}"

let empty = Str ""
