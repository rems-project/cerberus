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
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->
  c_frontend (conf, io) (stdlib, impl) ~filename

let hafnium_path =
  try Sys.getenv "HAFNIUM_PATH" with Not_found ->
    Pp_errors.fatal "environment variable HAFNIUM_PATH not set"

let cpp_cmd =
  Printf.sprintf
    "cc -E -C -Werror -nostdinc -undef -D__cerb__ -I%s/runtime/libc/include \
    -I%s/inc -I%s/inc/vmapi -I%s/src/arch/aarch64/inc \
    -DDEBUG -DMAX_CPUS=4 -DMAX_VMS=2 -DHEAP_PAGES=10"
    Global_ocaml.cerb_path hafnium_path hafnium_path hafnium_path

let rustic filename =
  let open Exception in
  match frontend cpp_cmd filename with
  | Exception(err)          -> prerr_endline (Pp_errors.to_string err)
  | Result(_, None     , _) -> assert false
  | Result(_, Some(ast), _) -> Ail_to_coq.run filename ast

let _ =
  let open Cmdliner in
  let file =
    let (docv, doc) = ("FILE", "source C file") in
    Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv ~doc)
  in
  Term.(exit @@ eval (pure rustic $ file, info "Ail rustic"))
