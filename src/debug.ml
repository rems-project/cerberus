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
