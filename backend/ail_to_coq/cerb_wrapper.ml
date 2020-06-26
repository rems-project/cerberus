open Cerb_frontend
open Cerb_backend
open Pipeline

let (>>=)  = Exception.except_bind
let return = Exception.except_return

let io : Pipeline.io_helpers =
  let pass_message = let ref = ref 0 in fun str ->
    Debug_ocaml.print_success (Printf.sprintf "%i. %s" !ref str);
    incr ref; return ()
  in
  let set_progress _ = return () in
  let run_pp opts doc = run_pp opts doc; return () in
  let print_endline str = print_endline str; return () in
  let print_debug n mk_str = Debug_ocaml.print_debug n [] mk_str; return () in
  let warn mk_str = Debug_ocaml.warn [] mk_str; return () in
  {pass_message ; set_progress ; run_pp ; print_endline ; print_debug ; warn}

let impl_name =
  try Sys.getenv "IMPL_NAME" with Not_found ->
    "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let frontend cpp_cmd filename =
  let conf =
    { debug_level = 0 ; pprints = [] ; astprints = [] ; ppflags = []
    ; typecheck_core = false ; rewrite_core = false
    ; sequentialise_core = false ; cpp_cmd ; cpp_stderr = true }
  in
  Global_ocaml.(set_cerb_conf false Random false Basic false false false);
  Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->
  c_frontend (conf, io) (stdlib, impl) ~filename

let run_cpp cpp_cmd filename =
  let conf =
    { debug_level = 0 ; pprints = [] ; astprints = [] ; ppflags = []
    ; typecheck_core = false ; rewrite_core = false
    ; sequentialise_core = false ; cpp_cmd ; cpp_stderr = true }
  in
  Global_ocaml.(set_cerb_conf false Random false Basic false false false);
  cpp (conf, io) ~filename

let cpp_cmd includes nostd =
  let includes =
    if nostd then includes else
    let cerb_runtime = Cerb_runtime.runtime () in
    Filename.concat cerb_runtime "libc/include" :: includes
  in
  let includes = List.map (fun dir -> "-I" ^ dir) includes in
  let includes = String.concat " " includes in
  let defs = "-D__cerb__ -DDEBUG -DMAX_CPUS=4 -DMAX_VMS=2 -DHEAP_PAGES=10" in
  "cc -E -C -Werror -nostdinc -undef " ^ defs ^ " " ^ includes

(* A couple of things that the frontend does not seem to check. *)
let source_file_check filename =
  if not (Sys.file_exists filename) then
    Panic.panic_no_pos "File [%s] does not exist." filename;
  if Sys.is_directory filename then
    Panic.panic_no_pos "A file was expected, [%s] is a directory." filename;
  if not (Filename.check_suffix filename ".c") then
    Panic.panic_no_pos "File [%s] does not have the [.c] extension." filename

let c_file_to_ail cpp_includes cpp_nostd filename =
  let open Exception in
  source_file_check filename;
  match frontend (cpp_cmd cpp_includes cpp_nostd) filename with
  | Result(_, Some(ast), _) -> ast
  | Result(_, None     , _) ->
      Panic.panic_no_pos "Unexpected frontend error."
  | Exception((loc,err))    ->
  match err with
  | CPP(_) -> Panic.panic_no_pos "Failed due to preprocessor error."
  | _      ->
  let err = Pp_errors.short_message err in
  let (_, pos) =
    try Location_ocaml.head_pos_of_location loc with Invalid_argument(_) ->
      ("", "(Cerberus position bug)")
  in
  Panic.panic loc "Frontend error.\n%s\n\027[0m%s%!" err pos

let cpp_lines cpp_includes cpp_nostd filename =
  source_file_check filename;
  let str =
    match run_cpp (cpp_cmd cpp_includes cpp_nostd) filename with
    | Result(str)  -> str
    | Exception(_) -> Panic.panic_no_pos "Failed due to preprocessor error."
  in
  String.split_on_char '\n' str
