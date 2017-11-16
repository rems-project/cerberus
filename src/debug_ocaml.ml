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
  failwith str


let debug_level = ref 0

let get_debug_level () =
  !debug_level

let print_success msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Green] msg)

let print_debug level doms msg =
  if !debug_level >= level then
    prerr_endline Colour.(ansi_format [Red] ("(debug " ^ string_of_int level ^ "): " ^ msg ()))



let location_to_string loc =
  Location_ocaml.(
    match loc with
      | Loc_unknown ->
          "unknown location"
      | Loc_other str ->
          "other location:'" ^ str ^ "'"
      | Loc_point pos ->
          Printf.sprintf "%s:%d:%d:" pos.pos_fname pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol)
      | Loc_region (pos1, pos2, _) ->
          Printf.sprintf "%s:%d:%d - %d:%d"
            pos1.pos_fname pos1.pos_lnum (1+pos1.pos_cnum-pos1.pos_bol)
                           pos2.pos_lnum (1+pos2.pos_cnum-pos2.pos_bol)
  )


let print_debug_located level doms loc msg =
  print_debug level doms (fun () -> "(" ^ location_to_string loc ^ ") - " ^ msg ())

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
