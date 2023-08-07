(* Created by Victor Gomes 2016-02-08 *)
(* Some useful generic functions *)

let ( $ ) f x = f x

let ( % ) f g = (fun x -> f (g x))

let ( %% ) f g = (fun x y -> f x (g y))

let id = fun x -> x

let flip f a b = f b a

let apply f x = f x

let uncurry f = (fun (x, y) -> f x y)

module Option = struct
exception No_value

let case f g = function
  | Some x -> f x
  | None -> g ()

let map f = function
  | Some x -> Some (f x)
  | None -> None

let get x = case id (fun _ -> raise No_value) x

end

exception Unsupported of string
exception Unexpected of string

(* Debugging *)

module Debug =
struct

  let level = ref 0

  let print n msg =
    if !level >= n then Printf.fprintf stderr "[%d]: %s\n%!" n msg

  let warn msg  =
    if !level > 0 then Printf.fprintf stderr "\x1b[33m[ WARN  ]: %s\n\x1b[0m%!" msg

  let error msg =
    Printf.fprintf stderr "\x1b[31m[ ERROR ]: %s\n\x1b[0m%!" msg

  let warn_exception msg e =
    warn (msg ^ " " ^ Printexc.to_string e)

  let error_exception msg e =
    error (msg ^ " " ^ Printexc.to_string e)

end

let diff xs ys = List.filter (fun x -> not (List.mem x ys)) xs

let concatMap f xs = List.concat (List.map f xs)

(* NOTE: this function was added to OCaml 4.13.0 stdlib *)
let starts_with ~prefix str =
    try
      String.(equal prefix (sub str 0 (length prefix)))
    with
      | Invalid_argument _ -> false

let remove_prefix ~prefix ?(trim_end=0) str =
  if starts_with ~prefix str then
    let n = String.length prefix in
    try Some (String.sub str n (String.length str - n - trim_end)) with
      | _ -> None
  else
    None

let is_power_of_two (n: Nat_big_num.num) : bool =
  let open Z in
  if equal n zero then
    false
  else
    n land (pred n) = zero

external terminal_size: unit -> (int * int) option = "terminal_size"