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
        fun str -> Debug_ocaml.print_success (string_of_int !ref ^ ". " ^ str);
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
      fun n mk_str -> Debug_ocaml.print_debug n [] mk_str;
                      return ()
      end;
    warn = begin
      fun mk_str -> Debug_ocaml.warn [] mk_str;
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
  Cerb_frontend.Ocaml_implementation.(set (MorelloImpl.impl));
  (* TODO(CHERI): make sure `SW_zap_dead_pointers` is unset *)
  Switches.set ["strict_pointer_equality"; "CHERI"] ;
  load_core_stdlib ()                                  >>= fun stdlib ->
  load_core_impl stdlib impl_name                      >>= fun impl   ->
  c_frontend (conf, io) (stdlib, impl) ~filename


let cpp_str runtime_path traditional =
  Printf.sprintf
    "clang %s -E -C -Werror -Wno-builtin-macro-redefined -nostdinc -undef -D__cerb__ -I %s/libc/include"
    (if traditional then "-traditional" else "")
    runtime_path

let cheri exec debug_level core_file runtime_path traditional filename =
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
    Global_ocaml.(set_cerb_conf exec Random false Basic false false false false);
    load_core_stdlib ()                                  >>= fun stdlib ->
    load_core_impl stdlib impl_name                      >>= fun impl   ->
    c_frontend (conf, io) (stdlib, impl) ~filename in
  match frontend (cpp_str runtime_path traditional) filename with
  | Exception.Exception err ->
     prerr_endline (Pp_errors.to_string err)
  | Exception.Result (_, _, file) ->
     begin
       (* Save CORE file if requested *)
       match core_file with
       | None -> ()
       | Some core_file ->
          let f = open_out core_file in
          Colour.do_colour := false ;
          PPrint.ToChannel.pretty 1.0 80 f (Pp_core.WithLocationsAndStd.pp_file file);
          close_out f
     end
(* Core_peval.boom file *)

open Cmdliner

let file =
  let doc = "source Core file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)

let traditional =
  let doc = "use \"traditional\" pre-processor" in
  Arg.(value & flag & info ["t";"traditional"] ~doc)

let runtime_path =
  let doc = "cerberus runtime directory" in
  let opam_runtime = (Sys.getenv "OPAM_SWITCH_PREFIX") ^ "/lib/cerberus/runtime" in
  Arg.(value & opt string opam_runtime & info ["r";"runtime"] ~docv:"DIR" ~doc)

let core_file =
  let doc = "save Core to file" in
  Arg.(value & opt (some string) None & info ["core"] ~docv:"FILE" ~doc)

let debug_level =
  let doc = "Set the debug message level to $(docv) (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let () =
  let cheri_t = Term.(pure cheri $exec $ debug_level $ core_file $ runtime_path $ traditional $ file) in
  Term.exit @@ Term.eval (cheri_t, Term.info "Core cheri")
