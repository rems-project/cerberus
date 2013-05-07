open Global

let outOfHomeomorphism msg = Pervasives.failwith ("[OutOfHomeomorphism exception>\n" ^ msg)

let assert_false msg = Pervasives.failwith ("[Impossible error>\n" ^ msg)

let debug str = Pervasives.failwith ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m")

let print_debug str k =
  if !Settings.debug then
    Pervasives.print_endline ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m");
  k

(* HACK *)
(*type char = char *)

let is_digit = function
  | '0' -> true
  | '1' -> true
  | '2' -> true
  | '3' -> true
  | '4' -> true
  | '5' -> true
  | '6' -> true
  | '7' -> true
  | '8' -> true
  | '9' -> true
  | _   -> false


let is_quote = function
  | '\'' -> true
  | _    -> false

let string_to_list str =
  let rec f k acc =
    if k < 0 then acc
             else f (k-1) (str.[k] :: acc)
  in f (String.length str - 1) []

(* AHEM *)
let list_to_string l =
  String.concat "" (List.map (String.make 1) l)


let rec span p = function
  | []             -> ([], [])
  | (x::xs') as xs -> if p x then let (ys,zs) = span p xs' in (x::ys, zs)
                             else ([], xs)

let span_string f str =
  let(xs, ys) = span f (string_to_list str) in
  (list_to_string xs, list_to_string ys)

let unquote_string str =
  let l = String.length str - 1 in
  if str.[0] <> '\'' || str.[l] <> '\'' then
    failwith ("Boot.unquote_string: found an unquoted string: " ^ str)
  else
    String.sub str 1 (l-1)



let splitAt_string k str =
  let (xs, ys) = splitAt k (string_to_list str) in
  (list_to_string xs, list_to_string ys)

let length_string = String.length

let pickList = function
  | []  -> failwith ""
  | [x] -> ([], x, [])
  | xs  -> let l = List.length xs in
           let (ys,z::zs) = splitAt (Random.int l) xs in
           (ys, z, zs)






(* Pretty printing *)
let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str

let pp_ail_ctype ty = to_plain_string $ Pp_ail.pp_ctype ty
let pp_core_expr e = to_plain_string $ Pp_core.pp_expr e
