open Symbol
open Pp_prelude


let to_string (Symbol (n, str_opt)) =
  let str = match str_opt with | Some str -> str | None -> "a" in
  str ^ "_" ^ string_of_int n

let to_string_pretty (Symbol (n, name_opt) as s) =
  match name_opt with
    | Some name ->
        if !Debug.debug_level > 0 then
          name ^ "{" ^ string_of_int n ^ "}"
        else
          name
    | None      -> to_string s

(*
let to_string_latex (n, _) =
  "v" ^ "_" ^ "{" ^ string_of_int n ^ "}"

let to_string_id (n, _) = string_of_int n
*)


let rec pp_prefix = function
  | [] ->
      P.empty
  | sym :: pref ->
      !^ (to_string_pretty sym) ^^ P.dot ^^ pp_prefix pref
