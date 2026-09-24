open Cerb_frontend
open Cerb_backend
open Pipeline

let (>>=) = Result.bind
let _return = Result.ok

let io = Pipeline.default_io_helpers

let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let frontend cpp_str filename =
  let conf = {
      debug_level= 0
    ; pprints= []
    ; astprints= []
    ; ppflags= []
    ; ppouts= []
    ; typecheck_core= false
    ; rewrite_core= false
    ; sequentialise_core= false
    ; cpp_cmd= cpp_str
    ; cpp_stderr= true
    ; cpp_save= None
  } in
  let open Cerb_global in
  let exec = false
  and exec_mode = Random
  and concurrency = false
  and defacto = false
  and permissive = false
  and agnostic = false
  and ignore_bitfields = false in
  Cerb_global.set_cerb_conf ~backend_name:"Ail_playground" ~exec exec_mode ~concurrency QuoteStd ~defacto ~permissive ~agnostic ~ignore_bitfields;
  load_core_stdlib ()                                  >>= fun stdlib ->
  load_core_impl stdlib impl_name                      >>= fun impl   ->
  c_frontend_and_elaboration (conf, io) (stdlib, impl) ~filename


let cpp_str =
    "cc -std=c11 -E -C -Werror -nostdinc -undef -D__cerb__"
  ^ " -I/Users/catzilla/rems-project/cerberus-private/runtime/libc/include"
  ^ " -I/Users/catzilla/github/hafnium/inc"
  ^ " -I/Users/catzilla/github/hafnium/inc/vmapi"
  ^ " -I/Users/catzilla/github/hafnium/src/arch/aarch64/inc"
  ^ " -DDEBUG"
  ^ " -DMAX_CPUS=4"
  ^ " -DMAX_VMS=2"
  ^ " -DHEAP_PAGES=10"


let learn (*out*) filename =
  match frontend cpp_str filename with
    | Result.Error err ->
        prerr_endline (Pp_errors.to_string err)
    | Result.Ok (_, None, _) ->
        assert false
    | Result.Ok (_, Some ail_file, _) ->
        failwith "Do something with the ail_file"


open Cmdliner

let file =
  let doc = "source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let () =
  let simpl_t = Term.(const (*query*) learn $ file) in
  Stdlib.exit @@ Cmd.eval (Cmd.(v (info "core-simpl") simpl_t))
