open Lexing

type domain =
  | DB_clexer
  | DB_cparser
  | DB_desugaring
  | DB_ail_typing
  | DB_elaboration
  | DB_core_typing
  | DB_core_dynamics
  | DB_driver
  | DB_concurrency
  | DB_driver_step
  | DB_memory

type debug_state = {
  level:   int;
  domains: domain list; (* using all domains if the list is empty *)
}





let error str =
  prerr_string (Colour.ansi_format [Red] "internal error: ");
  prerr_endline str;
  failwith @@ "internal error: " ^ str


let debug_level = ref 0

let get_debug_level () =
  !debug_level

let print_success msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Green] msg)

let print_debug level doms msg =
  if !debug_level >= level then
    prerr_endline Colour.(ansi_format [Red] ("(debug " ^ string_of_int level ^ "): " ^ msg ()))


let print_debug_located level doms loc msg =
  print_debug level doms (fun () -> "(" ^ Location_ocaml.location_to_string loc ^ ") - " ^ msg ())

let warn doms msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Yellow] ("WARNING: " ^ msg ()))

let print_debug2 msg k =
  if !debug_level > 0 then
    let _ = prerr_endline Colour.(ansi_format [Red] ("\x1b[31mDEBUG: " ^ msg ^ "\x1b[0m")) in k
  else
    k

let output_string2 msg =
  if !debug_level > 0 then
    prerr_endline msg




let timing_stack =
  ref []

let begin_timing (fun_name: string) =
  if !debug_level > 8 then
    timing_stack := (fun_name, Unix.gettimeofday ()) :: !timing_stack

let end_timing () =
  if !debug_level > 8 then
    let t' = Unix.gettimeofday () in
    match !timing_stack with
      | [] ->
          () (* this implies an improper use of end_timing, but we silently ignore *)
      | (str, t) :: xs ->
          let oc = open_out_gen [Open_creat; Open_wronly; Open_append] 0o666 "cerb.prof" in
          Printf.fprintf oc "[%s] %f\n" str (t' -. t);
          close_out oc;
          timing_stack := xs
