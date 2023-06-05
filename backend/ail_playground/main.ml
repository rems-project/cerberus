open Cerb_frontend
open Cerb_backend
open Pipeline

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

let io =
  let open Pipeline in
  { pass_message = begin
        let ref = ref 0 in
        fun str -> Cerb_debug.print_success (string_of_int !ref ^ ". " ^ str);
                   incr ref;
                   return ()
      end;
    set_progress = begin
      fun str -> return ()
      end;
    run_pp = begin
      fun opts doc -> run_pp opts doc;
                      return ()
      end;
    print_endline = begin
      fun str -> print_endline str;
                 return ();
      end;
    print_debug = begin
      fun n mk_str -> Cerb_debug.print_debug n [] mk_str;
                      return ()
      end;
    warn = begin
      fun mk_str -> Cerb_debug.warn [] mk_str;
                    return ()
      end;
  }


let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let frontend cpp_str filename =
  let conf = {
      debug_level= 0
    ; pprints= []
    ; astprints= []
    ; ppflags= []
    ; typecheck_core= false
    ; rewrite_core= false
    ; sequentialise_core= false
    ; cpp_cmd= cpp_str
    ; cpp_stderr= true
  } in
  Cerb_global.(set_cerb_conf "Ail_playground" false Random false Basic false false false false);
  load_core_stdlib ()                                  >>= fun stdlib ->
  load_core_impl stdlib impl_name                      >>= fun impl   ->
  c_frontend (conf, io) (stdlib, impl) ~filename


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
    | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err)
    | Exception.Result (_, None, _) ->
        assert false
    | Exception.Result (_, Some ail_file, _) ->
        failwith "Do something with the ail_file"


open Cmdliner

let file =
  let doc = "source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let () =
  let simpl_t = Term.(const (*query*) learn $ file) in
  Stdlib.exit @@ Cmd.eval (Cmd.(v (info "core-simpl") simpl_t))
