(* Created by Victor Gomes 2016-02-08 *)

(* NOTE: this function was added to OCaml 4.13.0 stdlib *)
let starts_with ~prefix str =
    try
      String.(equal prefix (sub str 0 (length prefix)))
    with
      | Invalid_argument _ -> false

(* NOTE: a corresponding function will be added in OCaml 5.6 *)
let remove_prefix ~prefix ?(trim_end=0) str =
  if starts_with ~prefix str then
    let n = String.length prefix in
    try Some (String.sub str n (String.length str - n - trim_end)) with
      | _ -> None
  else
    None

let is_power_of_two (n: Z.t) : bool =
  let open Z in
  if equal n zero then
    false
  else
    n land (pred n) = zero

external terminal_size: unit -> (int * int) option = "terminal_size"