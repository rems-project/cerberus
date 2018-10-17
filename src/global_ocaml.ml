let ($) f x = f x
let (|-) f g x = g (f x)
let (-|) f g x = f (g x)
let (>?>) x b f g = if b then f x else g x


(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"

(*
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
*)

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

type pp_flag =
  | Annot
  | FOut

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type cerberus_conf = {
  cpp_cmd:            string;
  pps:                language list;
  ppflags:            pp_flag list;
  exec_mode_opt:      Smt2.execution_mode option;
  ocaml:              bool;
  ocaml_corestd:      bool;
  progress:           bool;
  rewrite:            bool;
  sequentialise:      bool;
  concurrency:        bool;
  preEx:              bool;
  error_verbosity:    error_verbosity;
  batch:              bool;
  experimental_unseq: bool;
  typecheck_core:     bool;
  defacto:            bool;
  default_impl:       bool;
  action_graph:       bool;
  bmc:                bool;
  n1507:              Yojson.Basic.json option;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")


(* TODO: temporary, should use the field in cerb_conf *)
let cerb_exec_mode_opt =
  ref (Some Smt2.Random)

let current_execution_mode () =
(*  !!cerb_conf.exec_mode_opt *)
  !cerb_exec_mode_opt

let isDefacto () =
  !!cerb_conf.defacto

let show_action_graph () =
  !!cerb_conf.action_graph

(* print an error fatal message and exit with a given code *)
let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] $ "ERROR: " ^ msg);
  exit code

let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location cerberus."


let set_cerb_conf cpp_cmd pps ppflags exec exec_mode progress rewrite
                  sequentialise concurrency preEx ocaml ocaml_corestd error_verbosity batch experimental_unseq
                  typecheck_core defacto default_impl action_graph
                  bmc =
  cerb_exec_mode_opt := if exec then Some exec_mode else None;
  let conf = {
    cpp_cmd=       cpp_cmd;
    pps=           pps;
    ppflags=       ppflags;
    exec_mode_opt= if exec then Some exec_mode else None;
    ocaml=         ocaml;
    ocaml_corestd= ocaml_corestd;
    progress=      progress;
    rewrite=       rewrite;
    sequentialise= sequentialise || ocaml;
    concurrency=   concurrency || preEx;
    preEx=         preEx;
    error_verbosity= error_verbosity;
    batch=         batch;
    experimental_unseq= experimental_unseq;
    typecheck_core=typecheck_core;
    defacto=       defacto;
    default_impl=  default_impl;
    action_graph=  action_graph;
    bmc=           bmc;
    n1507=         if error_verbosity = QuoteStd then Some (Yojson.Basic.from_file (cerb_path ^ "/tools/n1570.json")) else None;
  } in
  cerb_conf := fun () -> conf


(* TODO: hack *)
let progress_sofar = ref 1


(* some block functions used by the pipeline *)
let pass_through        f = Exception.except_fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.except_fmap (fun v -> if b then f v else (); v)
let pass_message      msg = Exception.except_fmap (fun v -> Debug_ocaml.print_success msg; v)
let return_none m         = Exception.except_bind m (fun _ -> Exception.except_return None)
let return_empty m        = Exception.except_bind m (fun _ -> Exception.except_return [])

let return_value m        = Exception.except_bind m (fun _ -> Exception.except_return [])





let user_request_driver (strs: string list) : int =
  print_endline "HERE ARE THE POSSIBLE MOVES:";
  List.iteri (fun n str ->
    Printf.printf "Choice %d:\n%s\n\n" n str;
  ) strs;
  print_string "YOUR CHOICE: ";
  Pervasives.read_int ()


let concurrency_mode () =
  !!cerb_conf.concurrency





let new_int =
  let counter = ref 0 in
  fun () ->
    let n = !counter in
    incr counter;
    if n > !counter then
      assert false (* overflow *)
    else
      n
