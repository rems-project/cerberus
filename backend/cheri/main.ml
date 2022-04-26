open Cerb_frontend
open Cerb_backend
open Pipeline

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

let io, get_progress =
  let open Pipeline in
  let progress = ref 0 in
  { pass_message = begin
        let ref = ref 0 in
        fun str -> Debug_ocaml.print_success (string_of_int !ref ^ ". " ^ str);
                   incr ref;
                   return ()
      end;
    set_progress = begin
      fun _   -> incr progress;
                 return ()
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
  }, fun () -> !progress

let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let cpp_str runtime_path traditional =
  Printf.sprintf
    "clang %s -E -C -Werror -Wno-builtin-macro-redefined -nostdinc -undef -D__cerb__ -I %s/libc/include"
    (if traditional then "-traditional" else "")
    runtime_path

let cheri exec core_obj trace progress batch debug_level core_file runtime_path traditional filename =
  Debug_ocaml.debug_level := debug_level;
  let frontend cpp_str filename =
    let conf = {
        debug_level= debug_level
      ; pprints= []
      ; astprints= []
      ; ppflags= []
      ; typecheck_core= true
      ; rewrite_core= false
      ; sequentialise_core= false
      ; cpp_cmd= cpp_str
      ; cpp_stderr= true
      } in
    Cerb_runtime.specified_runtime := Some runtime_path;
    Cerb_frontend.Ocaml_implementation.(set (MorelloImpl.impl));
    (* `SW_zap_dead_pointers` should not be set *)
    Switches.set ["strict_pointer_equality";
                  "strict_pointer_arith";
                  "strict_reads";
                  "CHERI"] ;
    Global_ocaml.(set_cerb_conf exec Random false Basic false false false false);
    load_core_stdlib () >>= fun stdlib ->
    load_core_impl stdlib impl_name >>= fun impl ->
    begin
      if Filename.check_suffix filename ".core" then
        core_frontend (conf, io) (stdlib, impl) ~filename
        >>= core_passes (conf, io) ~filename >>= fun core_file ->
        return (None, None, core_file)
      else if Filename.check_suffix filename ".co" then
        let core_file = read_core_object (stdlib, impl) filename in
        return (None, None, core_file)
      else if Filename.check_suffix filename ".c" then
        c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (tunit_opt, ail_opt, core_file) ->
        core_passes (conf, io) ~filename core_file     >>= fun core_file'                      ->
        return (tunit_opt, ail_opt, core_file')
      else
        Exception.fail (Location_ocaml.unknown,
                        Errors.UNSUPPORTED
                          "The file extention is not supported")
    end in
  (* return (tunit_opt, ail_opt, core_file') in *)
  let epilogue n =
    if batch = `Batch then
      Printf.fprintf stderr "Time spent: %f seconds\n" (Sys.time ());
    if progress then get_progress ()
    else n
  in
  let runM = function
    | Exception.Exception err ->
       prerr_endline (Pp_errors.to_string err);
       epilogue 1
    | Exception.Result (Either.Left execs) ->
       List.iter print_string execs;
       epilogue 0
    | Exception.Result (Either.Right n) ->
       epilogue n
  in
  match frontend (cpp_str runtime_path traditional) filename with
  | Exception.Exception err ->
     prerr_endline (Pp_errors.to_string err) ;
     exit 1
  | Exception.Result (_, _, file) ->
     begin
       (* Save CORE object file if requested *)
       if core_obj then
         let output_file = Filename.remove_extension filename ^ ".co" in
         write_core_object file output_file;

       (* Save CORE file if requested *)
       match core_file with
       | None -> ()
       | Some core_file ->
          let f = open_out core_file in
          Colour.do_colour := false ;
          let pp_file =
            if Debug_ocaml.get_debug_level () > 0 then
              Pp_core.WithLocationsAndStd.pp_file
            else
              Pp_core.Basic.pp_file in
          PPrint.ToChannel.pretty 1.0 80 f (pp_file file);
          close_out f
     end ;
     if exec then
       let open Exhaustive_driver in
       let () = Tags.set_tagDefs file.tagDefs in
       let driver_conf = {concurrency=false;
                          experimental_unseq=false;
                          exec_mode=Random;
                          fs_dump=false;
                          trace} in
       runM @@ interp_backend io file ~args:[] ~batch ~fs:None ~driver_conf
     else
       exit 0

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

let core_obj =
  let doc = "Run frontend generating a target '.co' core object file." in
  Arg.(value & flag & info ["c"] ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let trace =
  let doc = "trace memory actions" in
  Arg.(value & flag & info["trace"] ~doc)

let progress =
  let doc = "Progress mode: the return code indicate how far the source program \
             went through the pipeline \
             [1 = total failure, 10 = parsed, 11 = desugared, 12 = typed, \
             13 = elaborated, 14 = executed]" in
  Arg.(value & flag & info ["progress"] ~doc)

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & vflag `NotBatch & [(`Batch, info["batch"] ~doc);
                                  (`CharonBatch, info["charon-batch"]
                                     ~doc:(doc^" (for Charon)"))])

let () =
  let cheri_t = Term.(pure cheri $ exec $ core_obj $ trace $ progress $ batch $ debug_level $ core_file $ runtime_path $ traditional $ file) in
  let version = Version.version in
  let info = Term.info "cerberus" ~version ~doc:"Cerberus CHERI C semantics"  in
  Term.exit_status @@ Term.eval (cheri_t, info)
