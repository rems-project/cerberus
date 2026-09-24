open Cerb_frontend
open Cerb_global
open Cerb_symbol

(* Pipeline *)

let (>>=) = Result.bind
let return = Result.ok

let run_pp fout_opt doc =
  let (is_fout, oc) =
    match fout_opt with
      | Some filename -> true, Stdlib.open_out filename
      | None -> false, Stdlib.stdout in
  let saved = !Cerb_colour.do_colour in
  Cerb_colour.do_colour := not is_fout;
  let term_col = match Cerb_util.terminal_size () with
    | Some (_, col) -> col
    | _ -> 80
  in
  PPrint.ToChannel.pretty 1.0 term_col oc doc;
  if is_fout then
    close_out oc;
  Cerb_colour.do_colour := saved

(* The path to the Core standard library *)
let core_stdlib_path () =
  Cerb_runtime.in_runtime "libcore"

(* == load the Core standard library ============================================================ *)
let load_core_stdlib () =
  let filename =
      if Switches.(has_switch SW_inner_arg_temps) then "std_inner_arg_temps.core" else "std.core" in
  let filepath = Filename.concat (core_stdlib_path ()) filename in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the Core standard library file\n (looked at: `" ^ filepath ^ "').")
  else
    Core_parser_driver.parse_stdlib filepath >>= function
    | Core_parser_util.Rstd (ailnames, std_funs) ->
      return (ailnames, std_funs)
    | _ ->
      error "while parsing the Core stdlib, the parser didn't recognise it as a stdlib."

(* == load the implementation file ============================================================== *)
let load_core_impl core_stdlib impl_name =
  let iname = Filename.concat (core_stdlib_path ()) ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists iname) then
    error ("couldn't find the implementation file\n (looked at: `" ^ iname ^ "').")
  else
    match Core_parser_driver.parse core_stdlib iname with
    | Ok (Core_parser_util.Rimpl impl_map) ->
      return impl_map
    | _ ->
      error "while parsing the Core impl, the parser didn't recognise it as an impl ."

let (>|>) m1 m2 =
  m1 >>= fun z  ->
  m2 >>= fun () ->
  return z

let whenM cond m =
  if cond then m () else return ()

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
  cpp_stderr: bool; (* pipe cpp stderr to stderr *)
  cpp_save: string option;
}

type io_helpers = {
  pass_message: string -> (unit, Errors.error) result;
  set_progress: string -> (unit, Errors.error) result;
  run_pp: string option -> PPrint.document -> (unit, Errors.error) result;
  print_endline: string -> (unit, Errors.error) result;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) result;
  warn: ?always:bool -> (unit -> string) -> (unit, Errors.error) result;
}

let (default_io_helpers, get_progress) =
  let progress = ref 0 in
  { pass_message = begin
        let ref = ref 0 in
        fun str -> Cerb_debug.print_success (Printf.sprintf "[%0.4f] %d. %s" (Sys.time ()) !ref str);
                   incr ref;
                   return ()
      end;
    set_progress = begin
      fun _   -> incr progress;
                 return ()
      end;
    run_pp = begin
      fun fout_opt doc -> run_pp fout_opt doc;
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
      fun ?(always=false) mk_str -> Cerb_debug.warn ~always [] mk_str;
                                    return ()
      end;
  }, fun () -> !progress

let cpp (conf, io) ~filename =
  io.print_debug 5 (fun () -> "C prepocessor") >>= fun () ->
  Unix.handle_unix_error begin fun () ->
    let (out_read, out_write) = Unix.pipe () in
    Unix.set_close_on_exec out_read;
    let out_ic = Unix.in_channel_of_descr out_read in
    let (err_ic_opt, err_write) =
      if conf.cpp_stderr then (None, Unix.stderr) else begin
        let (err_read, err_write) = Unix.pipe () in
        Unix.set_close_on_exec err_read;
        let err_ic = Unix.in_channel_of_descr err_read in
        (Some err_ic, err_write)
      end
    in
    let cpp_cmd = Str.split (Str.regexp "[ \t]+") conf.cpp_cmd in
    let cpp_args = Array.of_list @@ cpp_cmd @ [filename] in
    let cpp_pid = Unix.create_process (List.hd cpp_cmd) cpp_args
        Unix.stdin out_write err_write
    in
    Unix.close out_write;
    if not conf.cpp_stderr then Unix.close err_write;
    let rec read acc ic =
      try read (input_line ic :: acc) ic
      with End_of_file -> List.rev acc
    in
    flush_all ();
    let out = read [] out_ic in
    close_in out_ic;
    let err = match err_ic_opt with
      | Some err_ic ->
        let err = read [] err_ic in
        close_in err_ic;
        err
      | None -> []
    in
    match Unix.waitpid [] cpp_pid with
    | _, WEXITED n
    | _, WSIGNALED n
    | _, WSTOPPED n ->
      if n <> 0 then
        Result.error (Cerb_location.unknown, Errors.CPP (String.concat "\n" err))
      else
        let txt = String.concat "\n" out in
        (match conf.cpp_save with
        | None -> ()
        | Some cpp_file ->
          try 
            let out = open_out cpp_file in
            Printf.fprintf out "%s" txt;
            close_out out
          with e -> ()
        );
        return txt
  end ()

let c_frontend ?(cn_init_scope=Cn_desugaring.empty_init) (conf, io) (core_stdlib, core_impl) ~filename =
  Cerb_fresh.set_digest filename;
  let parse filename file_content =
    C_parser_driver.parse_from_string ~filename file_content >>= fun cabs_tunit ->
    io.set_progress "CPARS" >>= fun () ->
    io.pass_message "C parsing completed!" >>= fun () ->
    whenM (List.mem Cabs conf.astprints) begin
      fun () -> io.run_pp None (Pp_cabs.pp_translation_unit true true cabs_tunit)
    end >>= fun () ->
    whenM (List.mem Cabs conf.pprints) begin
      fun () -> io.warn (fun () -> "TODO: Cabs pprint to yet supported")
    end >>= fun () -> return cabs_tunit in
  (* -- *)
  let mk_pp_program pp fout_opt file =
    let fout_opt = List.assoc_opt Ail conf.ppouts in
    let saved = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := Unix.isatty Unix.stdout && Option.is_none fout_opt;
    let ret = pp file in
    Cerb_colour.do_colour := saved;
    ret in
  let desugar cabs_tunit =
    let (ailnames, core_stdlib_fun_map) = core_stdlib in
    Cabs_to_ail.desugar (ailnames, core_stdlib_fun_map, core_impl) cn_init_scope
      "main" cabs_tunit >>= fun (markers_env, ail_prog) ->
          io.set_progress "DESUG"
      >|> io.pass_message "Cabs -> Ail completed!"
          (* NOTE: if the debug level is lower the do the printing after the typing *)
      >|> whenM (conf.debug_level > 4 && List.mem Ail conf.astprints) begin
            fun () -> io.run_pp None (Pp_ail_ast.pp_program true false ail_prog)
          end
      >|> whenM (conf.debug_level > 4 && List.mem Ail conf.pprints) begin
            fun () ->
            let fout_opt = List.assoc_opt Ail conf.ppouts in
            io.run_pp fout_opt (mk_pp_program (Pp_ail.pp_program ~show_include:false) fout_opt ail_prog)
          end
      >>= fun () -> return (markers_env, ail_prog) in
  (* -- *)
  let ail_typechecking ail_prog =
    ErrorMonad.to_exception (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
      (GenTyping.annotate_program ail_prog) >>= fun (ailtau_prog, _) ->
    io.pass_message "Ail typing completed!" >>= fun () ->
    whenM (conf.debug_level <= 4 && List.mem Ail conf.astprints) begin
      fun () ->
        let doc = if conf.debug_level = 4 then
          (* (for debug 4) pretty-printing Ail with type annotations *)
          Pp_ail_ast.pp_program_with_annot ailtau_prog
        else
          Pp_ail_ast.pp_program true false ailtau_prog in
        io.run_pp None doc
    end >>= fun () ->
    whenM (conf.debug_level <= 4 && List.mem Ail conf.pprints) begin
      fun () ->
        let fout_opt = List.assoc_opt Ail conf.ppouts in
        let doc = if conf.debug_level = 4 then
          (* (for debug 4) pretty-printing Ail with type annotations *)
          mk_pp_program Pp_ail.pp_program_with_annot fout_opt ailtau_prog
        else
          mk_pp_program (Pp_ail.pp_program ~show_include:false) fout_opt ailtau_prog in
        io.run_pp fout_opt doc
    end >>= fun () -> return ailtau_prog in
  (* -- *)
  io.print_debug 2 (fun () -> "Using the C frontend") >>= fun () ->
  cpp (conf, io) ~filename    >>= fun file_content            ->
  parse filename file_content >>= fun cabs_tunit              ->
  desugar cabs_tunit          >>= fun (markers_env, ail_prog) ->
  ail_typechecking ail_prog   >>= fun ailtau_prog             ->
  return (cabs_tunit, (markers_env, ailtau_prog))

let c_frontend_and_elaboration ?(cn_init_scope=Cn_desugaring.empty_init) (conf, io) (core_stdlib, core_impl) ~filename =
  c_frontend ~cn_init_scope (conf, io) (core_stdlib, core_impl) ~filename >>= fun (cabs_tunit, (markers_env, ailtau_prog)) ->
  (* NOTE: the elaboration sets the struct/union tag definitions, so to allow the frontend to be
     used more than once, we need to do reset here *)
  (* TODO(someday): find a better way *)
  Tags.reset_tagDefs ();
  let calling_convention =
    Core.(if Switches.has_switch SW_inner_arg_temps then Inner_arg_callconv else Normal_callconv) in
  let core_file = Translation.translate core_stdlib calling_convention core_impl ailtau_prog in
  io.set_progress "ELABO" >>= fun () ->
  io.pass_message "Translation to Core completed!" >>= fun () ->
  return (Some cabs_tunit, Some (markers_env, ailtau_prog), core_file)

let core_frontend (conf, io) (core_stdlib, core_impl) ~filename =
  Cerb_fresh.set_digest filename;
  io.print_debug 2 (fun () -> "Using the Core frontend") >>= fun () ->
  Core_parser_driver.parse core_stdlib filename >>= function
    | Core_parser_util.Rfile (sym_main, globs, funs, tagDefs) ->
        (* Tags.set_tagDefs "Pipeline.core_frontend" tagDefs; *)
        return {
           Core.main=   Some sym_main;
           Core.calling_convention= Core.Normal_callconv; (* TODO *)
           Core.tagDefs= tagDefs;
           Core.stdlib= snd core_stdlib;
           Core.impl=   core_impl;
           Core.globs=  List.map (fun (s, bTy, e) -> (s, Core.GlobalDef (bTy, e))) globs;
           Core.funs=   funs;
           Core.extern=  Pmap.empty compare;
           Core.funinfo= Pmap.empty compare; (* TODO: need to parse funinfo! *)
           Core.loop_attributes0= Pmap.empty compare;
           Core.visible_objects_env= Pmap.empty compare;
         }
    | Core_parser_util.Rstd _ ->
        error "Found no main function in the Core program"
    | Core_parser_util.Rimpl _ ->
        failwith "core_frontend found a Rimpl"

(*
let pp_core (conf, io) ~filename core_file =
  let wrap_fout z = if List.mem FOut conf.ppflags then z else None in
  whenM (List.mem Core conf.astprints) begin
    fun () ->
      io.run_pp (wrap_fout (Some (filename, "core"))) (Ast_core.ast_file core_file)
  end >>= fun () ->
  whenM (List.mem Core conf.pprints) begin
    fun () ->
      io.run_pp (wrap_fout (Some (filename, "core"))) (Pp_core.Basic.pp_file core_file)
  end
*)

let core_rewrite (conf, io) core_file =
  let core_file2 = core_file in
  return (Core_rewrite.rewrite_file (core_file2))
  >|> whenM (conf.debug_level >= 6 && List.mem Core conf.astprints) begin
    fun () ->
      io.print_endline "BEGIN (before Core rewrite)" >>= fun () ->
      io.run_pp None (Ast_core.ast_file core_file)   >>= fun () ->
      io.print_endline "END"
  end
  >|> whenM (conf.debug_level >= 5 && List.mem Core conf.pprints) begin
    fun () ->
      io.print_endline "BEGIN (before Core rewrite)"   >>= fun () ->
      io.run_pp None (Pp_core.Basic.pp_file core_file) >>= fun () ->
      io.print_endline "END"
  end


let typed_core_passes (conf, io) core_file =
  whenM conf.typecheck_core begin
    fun () ->
      Core_typing.typecheck_program core_file >>= fun _ ->
      io.pass_message "Core typechecking completed!"
  end >>= fun () ->
  (* TODO: for now assuming a single order comes from indet expressions *)
  begin
    if conf.rewrite_core then core_rewrite (conf, io) core_file
    else return core_file
  end >>= fun core_file' ->
  (* NOTE: unlike the earlier call, this is typechecking after the rewriting and
     the indet passes *)
  Core_typing.typecheck_program core_file' >>= fun typed_core_file' ->
  let typed_core_file'' =
    if conf.sequentialise_core then
      Core_sequentialise.sequentialise_file typed_core_file'
    else
      typed_core_file' in
  return typed_core_file''

let print_core (conf, io) ~filename core_file =
  whenM (List.mem Core conf.astprints) begin
    fun () ->
      io.run_pp None (Pp_core_ast.pp_file core_file)
  end >>= fun () ->
  whenM (List.mem Core conf.pprints) begin
      fun () ->
      let fout_opt = List.assoc_opt Core conf.ppouts in
      let pp_file file =
        let saved = !Cerb_colour.do_colour in
        Cerb_colour.do_colour := Unix.isatty Unix.stdout && Option.is_none fout_opt;
        let ret = (match List.mem Annot conf.ppflags, List.mem Loc conf.ppflags with
                   | false, false -> Pp_core.Basic.pp_file
                   | false, true -> Pp_core.WithLocations.pp_file
                   | true, false -> Pp_core.WithStd.pp_file
                   | true, true -> Pp_core.WithLocationsAndStd.pp_file
                  ) file in
        Cerb_colour.do_colour := saved;
        ret in
      io.run_pp fout_opt (pp_file core_file)
  end >>= fun () ->
  return core_file

let core_passes (conf, io) ~filename core_file =
  (* If using the switch making load() returning unspecified value undefined, then
     we remove from the Core the code dealing with them. *)
  (* This is disabled for CHERI because some of the CHERI_intrinsics can
     return an unspecified value *)
  let rm_unspecs = Switches.(has_switch SW_strict_reads && not (is_CHERI ())) in
  let core_file =
    if rm_unspecs then
      Remove_unspecs.rewrite_file core_file
    else
      core_file in
  let core_file =
    if Switches.(has_switch SW_copy_prop) then
      Copy_propagation.transform_file ~unwrap_loaded:rm_unspecs core_file
    else
      core_file in
  if conf.sequentialise_core || conf.typecheck_core then
    typed_core_passes (conf, io) core_file >>= fun typed_core_file ->
    print_core (conf, io) ~filename typed_core_file >>= fun _ ->
    return core_file
  else if conf.rewrite_core then
    core_rewrite (conf, io) core_file >>= print_core (conf, io) ~filename
  else
    print_core (conf, io) ~filename core_file

let interp_backend io core_file ~args ~batch ~fs ~driver_conf =
  let module D = Driver_ocaml in
  let fs_state = match fs with
    | None -> Cerb_sibylfs.Fs_state.initial_state
    | Some fs -> Fs_ocaml.initialise fs
  in
  (* TODO: temporary hack for the command name *)
  match batch with
  | (`Batch | `CharonBatch | `JsonBatch) as mode ->
    let executions = D.batch_drive core_file ("cmdname" :: args) fs_state driver_conf in
    return (Either.Left (mode, executions))
  | `NotBatch ->
    let open Core in
    D.drive core_file ("cmdname" :: args) fs_state driver_conf >>= function
      | (Bloaded (LVspecified (OVinteger ival)) :: _) ->
          return (Either.Right begin
            match Mem.eval_integer_value ival with
              | Some n ->
                  begin try
                    Z.to_int n
                  with
                    | Z.Overflow ->
                        Cerb_debug.warn [] (fun () -> "Return value overlows (wrapping it down to 255)");
                        Z .(to_int (n mod (of_int 256)))
                  end 
              | None ->
                  Cerb_debug.warn [] (fun () -> "Return value was not a (simple) specified integer");
                  0
          end)
      | (cval :: _) ->
          io.warn (fun () -> "HELLO> " ^ String_core.string_of_value cval) >>= fun () ->
          return (Either.Right 0)
      | [] ->
          io.warn (fun () -> "BACKEND FOUND EMPTY RESULT") >>= fun () ->
          return (Either.Right 0)

(* NOTE: Every map needs to be serialised as associated lists, since marshalling
 * maps would require the flag Marshal.Closures. In this case, the output of
 * marshaling can only be read back in processes that run exactly the same
 * program, with exactly the same compiled code. *)
type 'a core_dump =
  { dump_main: Sym.t option;
    dump_calling_convention: Core.calling_convention;
    dump_tagDefs: (Sym.t * (Cerb_location.t * Ctype.tag_definition)) list;
    dump_globs: (Sym.t * 'a Core.generic_globs) list;
    dump_funs: (Sym.t * 'a Core.generic_fun_map_decl) list;
    dump_extern: (Identifier.t * (Sym.t list * Core.linking_kind)) list;
    dump_funinfo: (Sym.t * (Cerb_location.t * Annot.attributes * Ctype.ctype * (Sym.t option * Ctype.ctype) list * bool * bool)) list;
    (* dump_loop_attributes: (int * Annot.attributes) list; *)
  }

let map_from_assoc compare =
  List.fold_left (fun acc (k, v) -> Pmap.add k v acc) (Pmap.empty compare)

let version_info =
  Printf.sprintf "ocaml:%s+cerb:%s+mem:%s"
    (Sys.ocaml_version)
    (Version.version)
    (Impl_mem.name)

let read_core_object (conf, io) ?(is_lib=false) (core_stdlib, core_impl) filename =
  let open Core in
  let ic = open_in_bin filename in
  let v = input_line ic in
  if v <> version_info
  then
    Cerb_debug.warn [] (fun () -> "read core_object file produced with a different version of Cerberus => " ^ v);
  let dump: 'a core_dump = Marshal.from_channel ic in
  close_in ic;
  let core_file = { main=    dump.dump_main;
    calling_convention= dump.dump_calling_convention;
    tagDefs= map_from_assoc Sym.compare dump.dump_tagDefs;
    stdlib=  snd core_stdlib;
    impl=    core_impl;
    globs=   dump.dump_globs;
    funs=    map_from_assoc Sym.compare dump.dump_funs;
    extern=  map_from_assoc Identifier.compare dump.dump_extern;
    funinfo= map_from_assoc Sym.compare dump.dump_funinfo;
    loop_attributes0= Pmap.empty compare(* map_from_assoc compare dump.dump_loop_attributes *);
    visible_objects_env= Pmap.empty compare
  } in
  if not is_lib then
    print_core (conf, io) ~filename core_file
  else
    return core_file

let write_core_object core_file fname =
  let open Core in
  let dump: 'a core_dump =
    { dump_main = core_file.main;
      dump_calling_convention = core_file.calling_convention;
      dump_tagDefs = Pmap.bindings_list core_file.tagDefs;
      dump_globs = core_file.globs;
      dump_funs = Pmap.bindings_list core_file.funs;
      dump_extern = Pmap.bindings_list core_file.extern;
      dump_funinfo = Pmap.bindings_list core_file.funinfo;
(*      dump_loop_attributes = [] (*Pmap.bindings_list core_file.loop_attributes0*); *)
    }
  in
  let oc = open_out_bin fname in
  output_string oc (version_info ^ "\n");
  Marshal.to_channel oc dump [];
  close_out oc


(* FIXME: this is not working *)
(*
let ocaml_backend (conf, io) ~filename ~ocaml_corestd core_file =
  (* the OCaml backend really needs things to have been sequentialised *)
  (fun (_, typed_core) ->
     if conf.sequentialise_core then typed_core
     else Core_sequentialise.sequentialise_file typed_core)
  <$> typed_core_passes (conf, io) core_file
  >>= Codegen_ocaml.gen filename ocaml_corestd
*)


