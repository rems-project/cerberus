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
  cpp_cmd:           string;
  pps:               language list;
  core_stdlib:       unit Core.fun_map;
  core_impl:         unit Core.impl;
  core_parser:       Input.t -> (Core_parser_util.result, Errors.t9) Exception.t3;
  exec_mode_opt:     execution_mode option;
  progress:          bool;
  no_rewrite:        bool;
  concurrency:       bool;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")


(* TODO: temporary, should use the field in cerb_conf *)
let cerb_exec_mode_opt =
  ref (Some Exhaustive)

let current_execution_mode () =
(*  !!cerb_conf.exec_mode_opt *)
  !cerb_exec_mode_opt


let set_cerb_conf cpp_cmd pps core_stdlib core_impl exec exec_mode core_parser progress no_rewrite concurrency =
  cerb_exec_mode_opt := if exec then Some exec_mode else None;
  cerb_conf := fun () -> {
    cpp_cmd=       cpp_cmd;
    pps=           pps;
    core_stdlib=   core_stdlib;
    core_impl=     core_impl;
    core_parser=   core_parser;
    exec_mode_opt= if exec then Some exec_mode else None;
    progress=      progress;
    concurrency=   concurrency;
    no_rewrite=    no_rewrite
  }


(* print an error fatal message and exit with a given code *)
let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] $ "ERROR: " ^ msg);
  exit code


(* TODO: hack *)
let progress_sofar = ref 1


(* some block functions used by the pipeline *)
let pass_through        f = Exception.fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap (fun v -> if b then f v else (); v)
let pass_message      msg = Exception.fmap (fun v -> Debug.print_success msg; v)
let return_none m         = Exception.bind0 m (fun _ -> Exception.return0 None)
let return_empty m        = Exception.bind0 m (fun _ -> Exception.return0 [])

let return_value m        = Exception.bind0 m (fun _ -> Exception.return0 [])

