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
  | DB_core_rewriting

(*
type debug_state = {
  level:   int;
  domains: domain list; (* using all domains if the list is empty *)
}
*)

let error str =
  prerr_string (Cerb_colour.ansi_format ~err:true [Red] "internal error: ");
  prerr_endline str;
  failwith @@ "internal error: " ^ str

let debug_level = ref 0

let get_debug_level () =
  !debug_level

let print_success msg =
  if !debug_level > 0 then
    prerr_endline Cerb_colour.(ansi_format [Green] msg)

let print_debug level _doms msg =
  if !debug_level >= level then
    prerr_endline Cerb_colour.(ansi_format [Red] ("(debug " ^ string_of_int level ^ "): " ^ msg ()))

let print_debug_located level doms loc msg =
  print_debug level doms (fun () -> "[" ^ Cerb_location.location_to_string loc ^ "] - " ^ msg ())

let warn _doms msg =
  if !debug_level > 1 then
    prerr_endline Cerb_colour.(ansi_format [Yellow] ("WARNING: " ^ msg ()))

(*
let print_debug2 msg k =
  if !debug_level > 0 then
    let _ = prerr_endline Cerb_colour.(ansi_format [Red] ("\x1b[31mDEBUG: " ^ msg ^ "\x1b[0m")) in k
  else
    k
*)

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
         failwith "asd"
      | (str, t) :: xs ->
          let oc = open_out_gen [Open_creat; Open_wronly; Open_append] 0o666 "cerb.prof" in
          Printf.fprintf oc "[%s] %f\n" str (t' -. t);
          close_out oc;
          timing_stack := xs



let csv_timing_stack_file = ref None

let csv_timing_stack =
  ref []

let maybe_open_csv_timing_file () = 
  if !debug_level >= 1 then 
    begin
      let oc = open_out_gen [Open_creat; Open_wronly; Open_append] 0o666 "cerb_times.csv" in
      csv_timing_stack_file := Some oc;
      Printf.fprintf oc "action,time\n";
    end


let maybe_close_csv_timing_file () = 
  if !debug_level >= 1 then 
    match !csv_timing_stack_file with
    | None -> ()
    | Some oc ->
       assert (match !csv_timing_stack with [] -> true | _ -> false);
       close_out oc;
       csv_timing_stack_file := None


let begin_csv_timing () =
  if !debug_level >= 1 then
    csv_timing_stack := (Unix.gettimeofday ()) :: !csv_timing_stack

let end_csv_timing (fun_name: string) =
  match !csv_timing_stack_file with
  | None ->
     ()
  | Some oc ->
     let t' = Unix.gettimeofday () in
     match !csv_timing_stack with
     | [] ->
        error "empty timing stack when ending timing"
     | t :: xs ->
        Printf.fprintf oc "%s,%f\n" fun_name (t' -. t);
        csv_timing_stack := xs


