(*
module Loc = struct
  let of_tuple (file, line, _, _, _, _, _, _) = 
    "file: " ^ file ^ ", line: " ^ (string_of_int line)
end

(* Debug mode *)
let debug = true


let print msg = if debug then
                  print_endline ("\x1b[31m[DEBUG] " ^ msg ^ "\x1b[0m")(* "\x1b[31mDEBUG[" ^ __LOCATION__ ^ "]" *)
                else
                  ()

let error msg = print_endline ("\x1b[31m[ERROR] " ^ msg ^ "\x1b[0m"); exit 1
*)

let debug_level = ref 0

let print_success msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Green] msg)

let print_debug level msg =
  if !debug_level >= level then
    prerr_endline Colour.(ansi_format [Red] ("\x1b[31mDEBUG: " ^ msg ^ "\x1b[0m"))

let print_debug2 msg k =
  if !debug_level > 0 then
    let _ = prerr_endline Colour.(ansi_format [Red] ("\x1b[31mDEBUG: " ^ msg ^ "\x1b[0m")) in k
  else
    k

let output_string2 msg =
  if !debug_level > 0 then
    prerr_endline msg

