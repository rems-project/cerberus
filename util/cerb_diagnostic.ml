open Cerb_colour

let err_count = ref 0
let wrn_count = ref 0
let debug_level = ref 0

let finalise code =
  if !wrn_count > 0 then Printf.eprintf "%d warning generated.\n" !wrn_count;
  if !err_count > 0 then Printf.eprintf "%d error generated.\n" !err_count;
  exit code


exception Internal_error of string

let internal_error msg =
  Printf.eprintf "%s%s\n"
    (ansi_format ~err:true [Bold; Red] "internal error: ")
    msg;
  raise (Internal_error msg)

let fatal ?(code = 1) msg =
  incr err_count;
  prerr_endline (ansi_format ~err:true [Bold; Red] "error: " ^ ansi_format ~err:true [Bold] msg);
  let code = if code = 0 then 1 else code in
  finalise code

let warn ?(always=false) _doms msg =
  incr wrn_count;
  if always || !debug_level > 1 then
    prerr_endline Cerb_colour.(ansi_format [Yellow] ("warning: " ^ msg ()))
