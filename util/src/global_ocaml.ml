let (|-) f g x = g (f x)
let (-|) f g x = f (g x)
let (>?>) x b f g = if b then f x else g x

(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type execution_mode =
  | Exhaustive
  | Random

type cerberus_conf = {
  exec_mode_opt:      execution_mode option;
  concurrency:        bool;
  error_verbosity:    error_verbosity;
  defacto:            bool;
  n1570:              Yojson.Basic.json option;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")

(* print an error fatal message and exit with a given code *)
let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] @@ "ERROR: " ^ msg);
  exit code

let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location of Cerberus."


let set_cerb_conf exec exec_mode concurrency error_verbosity defacto bmc =
  let conf = { defacto; concurrency; error_verbosity;
    exec_mode_opt= if exec then Some exec_mode else None;
    n1570=         if error_verbosity = QuoteStd then
                     Some (Yojson.Basic.from_file (cerb_path ^ "/tools/n1570.json"))
                   else None;
  } in
  cerb_conf := fun () -> conf

let concurrency_mode () =
  !!cerb_conf.concurrency

let isDefacto () =
  !!cerb_conf.defacto

let current_execution_mode () =
  !!cerb_conf.exec_mode_opt

let verbose () =
  !!cerb_conf.error_verbosity

let n1570 () =
  !!cerb_conf.n1570

let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code
