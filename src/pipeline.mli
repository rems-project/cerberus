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
  unit -> ((string, Symbol.sym) Pmap.map * unit Core.fun_map, Location_ocaml.t * Errors.cause) Exception.exceptM

val load_core_impl:
  (string, Symbol.sym) Pmap.map * unit Core.fun_map -> string ->
  (Core.impl, Location_ocaml.t * Errors.cause) Exception.exceptM

val c_frontend:
  (configuration * io_helpers) ->
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  filename:string ->
  ( Cabs.translation_unit option
  * (GenTypes.genTypeCategory AilSyntax.ail_program) option
  * unit Core.file
  , Location_ocaml.t * Errors.cause) Exception.exceptM

val core_frontend:
  'a * io_helpers ->
  ('b * (Symbol.sym, (unit, unit) Core.generic_fun_map_decl) Pmap.map) *
  (Implementation_.implementation_constant, unit Core.generic_impl_decl)
  Pmap.map ->
  filename:string ->
  ((unit, unit) Core.generic_file, Location_ocaml.t * Errors.cause) Exception.exceptM

val core_passes:
  (configuration * io_helpers) -> filename:string -> unit Core.file ->
  (unit Core.file * unit Core.typed_file, Location_ocaml.t * Errors.cause) Exception.exceptM

val interp_backend:
  io_helpers -> 'a Core.file ->
  args:(string list) -> batch:[`Batch | `CharonBatch | `NotBatch] -> fs:string -> driver_conf:Exhaustive_driver.driver_conf ->
(* TODO: we would be using poly variants if it weren't for Lem... *)
(*  [`Interactive | `Exhaustive | `Random] -> *)
  ((string list, int) Either.either, Location_ocaml.t * Errors.cause) Exception.exceptM

val ocaml_backend:
  (configuration * io_helpers) -> filename:string -> ocaml_corestd:bool -> unit Core.file ->
  (int, Location_ocaml.t * Errors.cause) Exception.exceptM
