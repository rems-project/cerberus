let level = ref 0

let print n msg =
  if !level >= n then Printf.fprintf stderr "[%d]: %s\n%!" n msg

let warn msg =
  if !level > 0 then Printf.fprintf stderr "\x1b[33m[ WARN ]: %s\n\x1b[0m%!" msg

let error msg =
  Printf.fprintf stderr "\x1b[31m[ ERROR ]: %s\n\x1b[0m%!" msg

let error_exception msg e =
  error (msg ^ " " ^ Printexc.to_string e)
