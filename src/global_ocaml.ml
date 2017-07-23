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


type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type cerberus_conf = {
  cpp_cmd:            string;
  pps:                language list;
  core_stdlib:        (string, Symbol.sym) Pmap.map * unit Core.fun_map;
  core_impl_opt:      Core.impl option;
  core_parser:        Input.t -> (Core_parser_util.result, Errors.error) Exception.exceptM;
  exec_mode_opt:      execution_mode option;
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
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")


(* TODO: temporary, should use the field in cerb_conf *)
let cerb_exec_mode_opt =
  ref (Some Random)

let current_execution_mode () =
(*  !!cerb_conf.exec_mode_opt *)
  !cerb_exec_mode_opt

let isDefacto () =
  !!cerb_conf.defacto

let set_cerb_conf cpp_cmd pps core_stdlib core_impl_opt exec exec_mode core_parser progress rewrite
                  sequentialise concurrency preEx ocaml ocaml_corestd error_verbosity batch experimental_unseq
                  typecheck_core defacto =
  cerb_exec_mode_opt := if exec then Some exec_mode else None;
  cerb_conf := fun () -> {
    cpp_cmd=       cpp_cmd;
    pps=           pps;
    core_stdlib=   core_stdlib;
    core_impl_opt= core_impl_opt;
    core_parser=   core_parser;
    exec_mode_opt= if exec then Some exec_mode else None;
    ocaml=         ocaml;
    ocaml_corestd= ocaml_corestd;
    progress=      progress;
    rewrite=       rewrite;
    sequentialise= sequentialise || ocaml;
    concurrency=   concurrency || preEx;
    preEx=         preEx;
    error_verbosity= error_verbosity;
    batch= batch;
    experimental_unseq= experimental_unseq;
    typecheck_core= typecheck_core;
    defacto= defacto;
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
let pass_message      msg = Exception.fmap (fun v -> Debug_ocaml.print_success msg; v)
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
