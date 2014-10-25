let ($) f x = f x
let (|-) f g x = g (f x)
let (-|) f g x = f (g x)
let (>?>) x b f g = if b then f x else g x


(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"


type execution_mode =
  | Interactive
  | Exhaustive
  | Random

let string_of_execution_mode = function
  | Interactive ->
      "interactive"
  | Exhaustive ->
      "exhaustive"
  | Random ->
      "random"

type language =
  | Cabs
  | Ail
  | Core

let string_of_language = function
  | Cabs ->
      "cabs"
  | Ail ->
      "ail"
  | Core ->
      "core"


type cerberus_conf = {
  cpp_cmd:       string;
  pps:           language list;
  core_stdlib:   unit Core.fun_map;
  core_impl:     unit Core.impl;
  core_parser:   Input.t -> (Core_parser_util.result, Errors.t9) Exception.t3;
  exec_mode_opt: execution_mode option;
  progress:      bool;
  no_rewrite:    bool;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")

let set_cerb_conf cpp_cmd pps core_stdlib core_impl exec exec_mode core_parser progress no_rewrite =
  cerb_conf := fun () -> {
    cpp_cmd=       cpp_cmd;
    pps=           pps;
    core_stdlib=   core_stdlib;
    core_impl=     core_impl;
    core_parser=   core_parser;
    exec_mode_opt= if exec then Some exec_mode else None;
    progress=      progress;
    no_rewrite=    no_rewrite
  }


(* print an error fatal message and exit with a given code *)
let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] $ "ERROR: " ^ msg);
  exit code


let debug_level = ref 0

(* TODO: hack *)
let progress_sofar = ref 1


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




(* some block functions used by the pipeline *)
let pass_through        f = Exception.fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap (fun v -> if b then f v else (); v)
let pass_message      msg = Exception.fmap (fun v -> print_success msg; v)
let return_none m         = Exception.bind0 m (fun _ -> Exception.return0 None)
let return_empty m        = Exception.bind0 m (fun _ -> Exception.return0 [])

let return_value m        = Exception.bind0 m (fun _ -> Exception.return0 [])
