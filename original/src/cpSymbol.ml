type t = int * int * string option
type set = int ref * int

let init = ref 0
let inc s = s := !s + 1; !s

let make () = ref 0, inc init

let count (x, _) = !x

let fresh (x, c) = inc x, c, None
let fresh_name (x, c) name = inc x, c, Some name

let to_string (x, c, _) = "v" ^ BatInt.to_string c ^ "_" ^ BatInt.to_string x
let to_string_pretty ((_, _, name_opt) as s) =
  match name_opt with
  | Some n -> n
  | None -> to_string s

let to_string_latex (x, _, _) =
  "v" ^ "_" ^ "{" ^ BatInt.to_string x ^ "}"

let to_string_id (x, _, _) = BatInt.to_string x
