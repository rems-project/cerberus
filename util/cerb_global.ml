(*let (|-) f g x = g (f x)*)
let (-|) f g x = f (g x)
(*let (>?>) x b f g = if b then f x else g x*)

(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
(* external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply" *)

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type execution_mode =
  | Exhaustive
  | Random

type cerberus_conf = {
  backend_name:       string;
  exec_mode_opt:      execution_mode option;
  concurrency:        bool;
  error_verbosity:    error_verbosity;
  defacto:            bool;
  permissive:         bool; (* allows GCC extensions and stuff *)
  agnostic:           bool;
  ignore_bitfields:   bool;
  n1570:              Yojson.Basic.t option;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")

let set_cerb_conf ~backend_name ~exec exec_mode ~concurrency error_verbosity ~defacto ~permissive ~agnostic ~ignore_bitfields =
  let exec_mode_opt = if exec then Some exec_mode else None in
  let n1570 =
    if error_verbosity <> QuoteStd then None else Some (Lazy.force N1570.data)
  in
  let conf =
    {backend_name; defacto; concurrency; error_verbosity; agnostic; ignore_bitfields; permissive; exec_mode_opt; n1570}
  in
  cerb_conf := fun () -> conf

let backend_name () =
  !!cerb_conf.backend_name

let concurrency_mode () =
  !!cerb_conf.concurrency

let isDefacto () =
  !!cerb_conf.defacto

let isPermissive () =
  !!cerb_conf.permissive

let isAgnostic () =
  !!cerb_conf.agnostic

let isIgnoreBitfields () =
  !!cerb_conf.ignore_bitfields

let current_execution_mode () =
  !!cerb_conf.exec_mode_opt

let verbose () =
  !!cerb_conf.error_verbosity

let n1570 () =
  !!cerb_conf.n1570

let error ?(code = 1) msg =
  prerr_endline Cerb_colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code
