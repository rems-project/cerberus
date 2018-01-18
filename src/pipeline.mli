type language =
  | Cabs | Ail | Core

type pp_flag =
  | Annot | FOut

type configuration = {
  debug_level: int;
  pprints: language list;
  astprints: language list;
  ppflags: pp_flag list;
  typecheck_core: bool;
  rewrite_core: bool;
  sequentialise_core: bool;
  cpp_cmd: string;
  core_stdlib: (string, Symbol.sym) Pmap.map * unit Core.fun_map;
  core_impl: Core.impl;
}

type io_helpers = {
  pass_message: string -> (unit, Errors.error) Exception.exceptM;
  set_progress: string -> (unit, Errors.error) Exception.exceptM;
  run_pp: (string * string) option -> PPrint.document -> (unit, Errors.error) Exception.exceptM;
  print_endline: string -> (unit, Errors.error) Exception.exceptM;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) Exception.exceptM;
  warn: (unit -> string) -> (unit, Errors.error) Exception.exceptM;
}

val run_pp: (string * string) option -> PPrint.document -> unit

val load_core_stdlib:
  unit -> (string, Symbol.sym) Pmap.map * unit Core.fun_map

val load_core_impl:
  (Input.t -> (Core_parser_util.result, Location_ocaml.t * Errors.cause) Exception.exceptM) ->
  string -> Core.impl

val c_frontend:
  (configuration * io_helpers) -> filename:string ->
  ( Cabs.translation_unit option
  * (GenTypes.genTypeCategory AilSyntax.program) option
  * Symbol.sym
  * unit Core.file
  , Location_ocaml.t * Errors.cause) Exception.exceptM

val core_frontend:
  (configuration * io_helpers) -> filename:string ->
  ( Cabs.translation_unit option
  * (GenTypes.genTypeCategory AilSyntax.program) option
  * Symbol.sym
  * unit Core.file
  , Location_ocaml.t * Errors.cause) Exception.exceptM

val core_passes:
  (configuration * io_helpers) -> filename:string -> unit Core.file ->
  (unit Core.typed_file, Location_ocaml.t * Errors.cause) Exception.exceptM

val interp_backend:
  io_helpers -> Symbol.sym -> unit Core.file ->
  args:(string list) -> do_batch:bool -> concurrency:bool -> experimental_unseq:bool ->
  [`Interactive | `Exhaustive | `Random] ->
  (int, Location_ocaml.t * Errors.cause) Exception.exceptM

val ocaml_backend:
  (configuration * io_helpers) -> filename:string -> ocaml_corestd:bool -> Symbol.sym -> unit Core.file ->
  (int, Location_ocaml.t * Errors.cause) Exception.exceptM
