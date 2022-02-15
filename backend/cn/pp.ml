module CF = Cerb_frontend

include PPrint

(* copying from backend.ml *)
external get_terminal_size: unit -> (int * int) option = "terminal_size"

type doc = document

(* copying from backend.ml *)
let term_col = match get_terminal_size () with
  | Some (_, col) -> col - 1
  | _ -> 80 - 1


type loc_pp = 
  | Hex
  | Dec

let loc_pp = ref Dec



let int i = string (string_of_int i)


let unicode = ref true
let print_level = ref 0

(* from run_pp *)
let print channel doc = 
  PPrint.ToChannel.pretty 1.0 term_col channel (doc ^^ hardline);
  flush channel

(* adapting from pipeline.ml *)
let print_file filename doc = 
  let oc = open_out filename in
  print oc doc;
  close_out oc



let plain = CF.Pp_utils.to_plain_pretty_string
let (^^^) = Pp_prelude.(^^^)


let format_string format str = Colour.ansi_format format str

let format format string = 
  let n = String.length string in
  fancystring (format_string format string) n

let uformat format string n = 
  fancystring (format_string format string) n


type alignment = L | R

let pad_ alignment should_width has_width pp = 
  let diff = should_width - has_width in
  if diff < 0 then pp else 
    match alignment with
    | L -> pp ^^ repeat diff space
    | R -> repeat diff space ^^ pp

let pad alignment width pp = 
  pad_ alignment width (requirement pp) pp


let pad_string_ alignment should_width has_width pp = 
  let diff = should_width - has_width in
  if diff < 0 then pp else 
    match alignment with
    | L -> pp ^ String.make diff ' '
    | R -> String.make diff ' ' ^ pp


let pad_string alignment width pp = 
  pad_string_ alignment width (String.length pp) pp

let list f l = 
  match l with
  | [] -> !^"(empty)"
  | l -> flow_map (comma ^^ break 1) f l

let list_filtered f l = 
  match List.filter_map f l with
  | [] -> !^"(empty)"
  | l -> flow (comma ^^ break 1) l



let nats n =
  let rec aux n = if n < 0 then [] else n :: aux (n - 1) in
  List.rev (aux n)

module IntMap = Map.Make(Int)



let typ n typ = 
  n ^^^ colon ^^^ typ

let item item content = 
  format [Bold] item ^^ colon ^^ space ^^ align content

let c_comment pp = 
  !^"/*" ^^ pp ^^ !^"*/"

let c_app f args = 
  group (f ^^ group (parens (flow (comma ^^ break 1) args)))



let headline a = 
  (if !print_level >= 2 then hardline else empty) ^^
    format [Bold; Magenta] ("# " ^ a)

let bold a = format [Bold] a

let action a = format [Cyan] ("## " ^ a ^ " ")

let debug l pp = 
  if !print_level >= l 
  then
    let time = Sys.time () in
    let dpp = format [Green] ("[" ^ Float.to_string time ^ "] ") in
    print stderr (dpp ^^ Lazy.force pp)

let warn pp = 
  print stderr (format [Bold; Yellow] "Warning:" ^^^ pp)

let time_f level msg f x =
  if !print_level >= level 
  then
    let start = Sys.time () in
    let y = f x in
    let fin = Sys.time () in
    let d = fin -. start in
    debug level (lazy (format [] (msg ^ ": elapsed: " ^ Float.to_string d)));
    y
  else
    f x





(* stealing some logic from pp_errors *)
let error (loc : Locations.t) msg extras = 
  let (head, pos) = Locations.head_pos_of_location loc in
  print stderr (format [Bold; Red] "error:" ^^^ 
                format [Bold] head ^^^ msg);
  if Locations.is_unknown loc then () else print stderr !^pos;
  List.iter (fun pp -> print stderr pp) extras








(* stealing from debug_ocaml *)
let json_output_channel = ref None

let maybe_open_json_output mfile = 
  match mfile with
  | None -> 
     json_output_channel := None
  | Some file -> 
     let oc = open_out file in
     json_output_channel := Some oc;
     output_string oc "[\n"

let maybe_close_json_output () = 
  match !json_output_channel with
  | None -> 
     ()
  | Some oc -> 
     output_string oc "\n]";
     json_output_channel := None;
     close_out oc


let print_json =
  let first = ref true in
  fun json ->
  match !json_output_channel with
  | Some oc ->
     if !first then first := false else output_string oc ",\n";
     Yojson.Safe.pretty_to_channel ~std:true oc (Lazy.force json);
     output_char oc '\n'
  | _ -> ()




(* let progress_bar name total_number = 
 *   let module P = Progress in
 *   P.Line.list [
 *       P.Line.const "  "; P.Line.rpad 20 (P.Line.const name); 
 *       P.Line.count_to total_number;
 *       P.Line.bar ~color:(P.Color.ansi `cyan) total_number
 *     ] *)



let progress title total_number : (string -> unit) = 
  let counter = ref 0 in
  fun current ->
  let () = counter := !counter + 1 in
  let total_number_str = string_of_int total_number in
  let n = String.length total_number_str in
  let msg = 
    format [Blue] title ^^^ 
    brackets (
       !^(Printf.sprintf "%0*d" n !counter) ^^ slash ^^ 
       !^total_number_str
      ) ^^
    colon ^^^
    !^current
  in
  print stdout msg

  
