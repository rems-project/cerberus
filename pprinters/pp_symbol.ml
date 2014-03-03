open Symbol

let to_string (Symbol (n, _)) = "a" ^ "_" ^ string_of_int n

let to_string_pretty (Symbol (n, name_opt) as s) =
  match name_opt with
    | Some name -> name ^ "{" ^ string_of_int n ^ "}"
    | None      -> to_string s

let to_string_latex (n, _) =
  "v" ^ "_" ^ "{" ^ string_of_int n ^ "}"

let to_string_id (n, _) = string_of_int n
