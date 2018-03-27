open Instance_manager

let dummy_io =
  let open Pipeline in
  let skip = fun _ -> Exception.except_return ()
  in {
    pass_message=   skip;
    set_progress=   skip;
    run_pp=         (fun _ -> skip);
    print_endline=  skip;
    print_debug=    (fun _ -> skip);
    warn=           skip;
  }

let setup_cerb_conf cerb_debug_level cpp_cmd impl_filename =
  let open Pipeline in
  let core_stdlib = load_core_stdlib ()
  in {
    debug_level=         cerb_debug_level;
    pprints=             [];
    astprints=           [];
    ppflags=             [];
    typecheck_core=      false;
    rewrite_core=        true;
    sequentialise_core=  true;
    cpp_cmd=             cpp_cmd;
    core_stdlib=         core_stdlib;
    core_impl=           load_core_impl core_stdlib impl_filename;
  }

(* It would be nice if Smt2 could use polymorphic variant *)
let to_smt2_mode = function
  | Random -> Smt2.Random
  | Exhaustive -> Smt2.Exhaustive

(* TODO: this hack is due to cerb_conf be undefined when running Cerberus *)
let hack conf mode =
  let open Global_ocaml in
  cerb_conf := fun () -> {
    cpp_cmd=            conf.Pipeline.cpp_cmd;
    pps=                [];
    ppflags=            [];
    core_stdlib=        conf.Pipeline.core_stdlib;
    core_impl_opt=      Some conf.Pipeline.core_impl;
    core_parser=        (fun _ -> failwith "No core parser");
    exec_mode_opt=      Some (to_smt2_mode mode);
    ocaml=              false;
    ocaml_corestd=      false;
    progress=           false;
    rewrite=            conf.Pipeline.rewrite_core;
    sequentialise=      conf.Pipeline.sequentialise_core;
    concurrency=        false;
    preEx=              false;
    error_verbosity=    Global_ocaml.Basic;
    batch=              true;
    experimental_unseq= false;
    typecheck_core=     conf.Pipeline.typecheck_core;
    defacto=            false;
    default_impl=       false;
    action_graph=       false;
  }

(* elaboration *)

let elaborate ~conf ~filename =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack (fst conf) Random;
  print_endline ("Elaborating: " ^ filename);
  Debug_ocaml.print_debug 2 [] (fun () -> "Elaborating: " ^ filename);
  try
    Pipeline.c_frontend conf filename
    >>= function
    | (Some cabs, Some ail, sym_suppl, core) ->
      Pipeline.core_passes conf ~filename core
      >>= fun (core', _) ->
      return (cabs, ail, sym_suppl, core')
    | _ ->
      Exception.throw (Location_ocaml.unknown,
                       Errors.OTHER "fatal failure core pass")
  with
  | e ->
    Debug_ocaml.warn [] (fun () ->
        "Exception raised during elaboration. " ^ Printexc.to_string e
      ); raise e

let result_of_elaboration (cabs, ail, _, core) =
  let string_of_doc d =
    let buf = Buffer.create 1024 in
    PPrint.ToBuffer.pretty 1.0 80 buf d;
    Buffer.contents buf
  in
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let mk_elab d = Some (elim_paragraph_sym @@ string_of_doc d) in
  let (core, locs) =
    let module Param_pp_core = Pp_core.Make (struct
        let show_std = true
        let show_location = true
        let show_proc_decl = false
      end) in
    Colour.do_colour := false;
    Param_pp_core.pp_file core
    |> string_of_doc
    |> Location_mark.extract
  in Elaboration
    { pp= {
        cabs= None;
        ail=  mk_elab @@ Pp_ail.pp_program ail;
        core= Some (elim_paragraph_sym core)
      };
      ast= {
        cabs= mk_elab @@ Pp_cabs.pp_translation_unit false false cabs;
        ail=  mk_elab @@ Pp_ail_ast.pp_program ail;
        core = None;
      };
      locs= locs;
    }

(* execution *)

let execute ~conf ~filename (mode: exec_mode) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack (fst conf) mode;
  Debug_ocaml.print_debug 2 [] (fun () ->
      "Executing in " ^ string_of_exec_mode mode ^ " mode: " ^ filename
    );
  try
    elaborate ~conf ~filename
    >>= fun (cabs, ail, sym_suppl, core) ->
    Pipeline.interp_backend dummy_io sym_suppl core [] true false false
      (to_smt2_mode mode)
    >>= function
    | Either.Left res ->
      return (String.concat "\n" res)
    | Either.Right res ->
      return (string_of_int res)
  with
  | e ->
    Debug_ocaml.warn [] (fun () ->
        "Exception raised during execution." ^ Printexc.to_string e
      ); raise e

let respond f = function
  | Exception.Result r ->
    f r
  | Exception.Exception err ->
    Failure (Pp_errors.to_string err)

(* instance *)

module Instance : Instance = struct
  let pipe_conf =
    let impl = "gcc_4.9.0_x86_64-apple-darwin10.8.0" in
    let cpp_cmd = "cc -E -C -traditional-cpp -nostdinc -undef -D__cerb__ -I "
                ^ Pipeline.cerb_path ^ "/include/c/libc -I "
                ^ Pipeline.cerb_path ^ "/include/c/posix"
    in setup_cerb_conf 0 cpp_cmd impl

  let name = Ocaml_mem.name

  let instance_conf conf =
    let new_conf = { pipe_conf with Pipeline.rewrite_core= conf.rewrite }
    in (new_conf, dummy_io)

  let elaborate user_conf filename =
    let conf = instance_conf user_conf in
    elaborate ~conf ~filename
    |> respond result_of_elaboration

  let execute user_conf filename mode =
    let conf = instance_conf user_conf in
    execute ~conf ~filename mode
    |> respond (fun s -> Execution s)
end

let () =
  print_endline ("Loading " ^ Ocaml_mem.name);
  Instance_manager.add_model (module Instance)
