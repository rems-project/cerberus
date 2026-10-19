open Cerb_frontend

type language =
  | Cabs | Ail | Core | Types

type pp_flag =
  | Annot
  | Loc

type configuration = {
  debug_level: int;
  pprints: language list;
  astprints: language list;
  ppflags: pp_flag list;
  ppouts: (language * string) list;
  typecheck_core: bool;
  rewrite_core: bool;
  sequentialise_core: bool;
  cpp_cmd: string;
  cpp_stderr: bool;
  cpp_save: string option; (* Save the result of pre-processing to this file *)
}

type io_helpers = {
  pass_message: string -> (unit, Errors.error) Result.t;
  set_progress: string -> (unit, Errors.error) Result.t;
  run_pp: string option -> PPrint.document -> (unit, Errors.error) Result.t;
  print_endline: string -> (unit, Errors.error) Result.t;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) Result.t;
  warn: ?always:bool -> (unit -> string) -> (unit, Errors.error) Result.t;
}
val default_io_helpers: io_helpers
val get_progress: unit -> int

val run_pp: string option -> PPrint.document -> unit

val core_stdlib_path: unit -> string

val load_core_stdlib:
  unit -> ((string, Symbol.sym) Pmap.map * unit Core.fun_map, Cerb_location.t * Errors.cause) Result.t

val load_core_impl:
  (string, Symbol.sym) Pmap.map * unit Core.fun_map -> string ->
  (Core.impl, Cerb_location.t * Errors.cause) Result.t

val cpp: (configuration * io_helpers) -> filename:string -> (string, Cerb_location.t * Errors.cause) Result.t

val c_frontend:
  ?cn_init_scope: Cn_desugaring.init_scope ->
  Config.config ->
  (configuration * io_helpers) ->
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  filename:string ->
  ( Cabs.translation_unit
  * (Cabs_to_ail_effect.fin_markers_env * GenTypes.genTypeCategory AilSyntax.ail_program)
  , Cerb_location.t * Errors.cause) Result.t

val c_frontend_and_elaboration:
  ?cn_init_scope: Cn_desugaring.init_scope ->
  Config.config ->
  (configuration * io_helpers) ->
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  filename:string ->
  ( Cabs.translation_unit option
  * (Cabs_to_ail_effect.fin_markers_env * GenTypes.genTypeCategory AilSyntax.ail_program) option
  * unit Core.file
  , Cerb_location.t * Errors.cause) Result.t

val core_frontend:
  'a * io_helpers ->
  ('b * (Symbol.sym, (unit, unit) Core.generic_fun_map_decl) Pmap.map) *
  (Implementation.implementation_constant, unit Core.generic_impl_decl)
  Pmap.map ->
  filename:string ->
  ((unit, unit) Core.generic_file, Cerb_location.t * Errors.cause) Result.t


val typed_core_passes:
  (configuration * io_helpers) -> unit Core.file ->
  (unit Core.file * unit Core.typed_file, Cerb_location.t * Errors.cause) Result.t

val core_passes:
  (configuration * io_helpers) -> filename:string -> unit Core.file ->
  (unit Core.file, Cerb_location.t * Errors.cause) Result.t

val interp_backend:
  conf:Config.config ->
  io_helpers -> 'a Core.file ->
  args:(string list) -> batch:[`Batch | `CharonBatch | `JsonBatch | `NotBatch] -> fs:string option ->
  ((([`Batch | `CharonBatch | `JsonBatch] * (string list * Driver_ocaml.batch_output) list), int) Either.either, Cerb_location.t * Errors.cause) Result.t

(*
val ocaml_backend:
  (configuration * io_helpers) -> filename:string -> ocaml_corestd:bool -> unit Core.file ->
  (int, Cerb_location.t * Errors.cause) Result.t
   *)

val read_core_object:
  (configuration * io_helpers) -> ?is_lib:bool ->
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  string ->
  (unit Core.file, Cerb_location.t * Errors.cause) Result.t
val write_core_object: unit Core.file -> string -> unit


val untype_file: 
  'a Core.typed_file ->
  'a Core.file

val mk_config:
  backend_name:string ->
  agnostic:bool ->
  permissive:bool ->
  lexicon:Config.lexicon ->
  asm_keyword:bool ->
  cerb_keywords:bool ->
  cerb_builtins:bool ->
  ignore_bitfields:bool ->
  allow_distinct_ptr_types_comparison:bool ->
  allow_void_ptr_arithmetic:bool ->
  allow_void_return:bool ->
  execution_mode:Config.execution_mode option ->
  concurrency:bool ->
  do_stepping:bool ->
  do_tracing:bool ->
  fs_dump:bool ->
  Config.config
