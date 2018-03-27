open Prelude
    (*
open Instance_manager

(* Load Concrete and Symbolic instances of Cerberus *)

let load_instance fname =
  let fname = Dynlink.adapt_filename fname in
  if Sys.file_exists fname then
    try Dynlink.loadfile fname
    with
    | Dynlink.Error err ->
      error ("Loading memory model: " ^ Dynlink.error_message err);
  else error "File does not exists"

let () =
  Prelude.mem_switch := Prelude.MemConcrete;
  load_instance "./_build/src/memmodel.cma";
  Prelude.mem_switch := Prelude.MemSymbolic;
  load_instance "./_build/src/memmodel.cma";;
       *)

(* Pipeline *)

let run_pp with_ext doc =
  let (is_fout, oc) =
    match with_ext with
      | Some (filename, ext_str) ->
          (true, Pervasives.open_out (Filename.remove_extension (Filename.basename filename) ^ "." ^ ext_str))
      | None ->
          (false, Pervasives.stdout) in
  let saved = !Colour.do_colour in
  Colour.do_colour := not is_fout;
  (* TODO(someday): dynamically get the width of the terminal *)
  PPrint.ToChannel.pretty 1.0 80 oc doc;
  if is_fout then
    close_out oc;
  Colour.do_colour := saved


(* This is the symbol counter used by (I think) everything: Core parser,
   desugaring, elaboratiion ... *)
(* TODO(someday): find a clean way to get rid of that reference... *)
let sym_counter =
  ref 0


(* The path to where Cerberus is installed *)
let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location cerberus."

(* The path to the Core standard library *)
let core_stdlib_path =
  Filename.concat cerb_path "include/core"

(* TODO(someday): get rid of the Lexer_util and Input parametric stuff, we don't use it... *)
let load_core_stdlib () =
  let filepath = Filename.concat core_stdlib_path "std.core" in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the Core standard library file\n (looked at: `" ^ filepath ^ "').");
  Debug_ocaml.print_debug 5 [] (fun () ->
    "reading Core standard library from `" ^ filepath ^ "'."
  );
  (* A preliminary instance of the Core parser (on that doesn't know the
     definitions from the stdlib...) *)
  let module Core_std_parser =
    Parser_util.Make
      (struct
        include Core_parser.Make (struct
          let sym_counter = sym_counter (* NOTE: this is why we need a reference for the counter ... *)
          let mode = Core_parser_util.StdMode
          let std = Pmap.empty Core_parser_util._sym_compare
        end)
        type result = Core_parser_util.result
      end)
      (Lexer_util.Make (Core_lexer)) in
  (* TODO: maybe have a nicer handling of errors (though these are all fatal) *)
  match Core_std_parser.parse (Input.file filepath) with
    | Exception.Result (Core_parser_util.Rstd (ailnames, std_funs)) ->
        (ailnames, std_funs)
    | Exception.Result _ ->
        error "while parsing the Core stdlib, the parser didn't recognise it as a stdlib."
    | Exception.Exception err ->
        error ("[Core parsing error: stdlib] " ^ Pp_errors.to_string err)


let load_core_impl core_stdlib impl_name =
  let filepath = Filename.concat core_stdlib_path ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the implementation file\n (looked at: `" ^ filepath ^ "').");
  let module Core_parser =
    Parser_util.Make (struct
      include Core_parser.Make (struct
        let sym_counter = sym_counter
        let mode = Core_parser_util.ImplORFileMode
        let std = List.fold_left (fun acc (fsym, _) ->
          match fsym with
            | Symbol.Symbol (_, Some str) ->
                let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
                Pmap.add (str, (std_pos, std_pos)) fsym acc
            | Symbol.Symbol (_, None) ->
                 acc
        ) (Pmap.empty Core_parser_util._sym_compare) (Pmap.bindings_list (snd core_stdlib))
      end)
      type result = Core_parser_util.result
    end) (Lexer_util.Make (Core_lexer)) in
  (* TODO: maybe have a nicer handling of errors (though these are all fatal) *)
  match Core_parser.parse (Input.file filepath) with
    | Exception.Result (Core_parser_util.Rimpl impl_map) ->
        impl_map
    | Exception.Result (Core_parser_util.Rfile _ | Core_parser_util.Rstd _) ->
        assert false
    | Exception.Exception err ->
        error ("[Core parsing error: impl-file] " ^ Pp_errors.to_string err)


let return = Exception.except_return
let (>>=)  = Exception.except_bind
let (<$>)  = Exception.except_fmap

let (>|>) m1 m2 =
  m1 >>= fun z  ->
  m2 >>= fun () ->
  return z

let whenM cond m =
  if cond then m () else return ()

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
  core_stdlib: (string, Symbol.sym) Pmap.map * unit Core.fun_map;
  core_impl: Core.impl;
}

type io_helpers = {
  pass_message: string -> (unit, Errors.error) Exception.exceptM;
  set_progress: string -> (unit, Errors.error) Exception.exceptM;
  run_pp: (string * string) option -> PPrint.document -> (unit, Errors.error) Exception.exceptM;
  print_endline: string -> (unit, Errors.error) Exception.exceptM;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) Exception.exceptM;
  warn: (unit -> string) -> (unit, Errors.error) Exception.exceptM;
}


let c_frontend (conf, io) ~filename =
  let wrap_fout z = if List.mem FOut conf.ppflags then z else None in
  let open Debug_ocaml in
  (* -- *)
  let parse filename =
    Cparser_driver.parse (Input.file filename) >>= fun cabs_tunit ->
    io.set_progress "CPARS" >>= fun () ->
    io.pass_message "C parsing completed!" >>= fun () ->
    whenM (List.mem Cabs conf.astprints) begin
      fun () -> io.run_pp None (Pp_cabs.pp_translation_unit true true cabs_tunit)
    end >>= fun () ->
    whenM (List.mem Cabs conf.pprints) begin
      fun () -> io.warn (fun () -> "TODO: Cabs pprint to yet supported")
    end >>= fun () -> return cabs_tunit in
  (* -- *)
  let desugar cabs_tunit =
    let (ailnames, core_stdlib_fun_map) = conf.core_stdlib in
    Cabs_to_ail.desugar !sym_counter (ailnames, core_stdlib_fun_map, conf.core_impl)
      "main" cabs_tunit >>= fun (sym_suppl, ail_prog) ->
          io.set_progress "DESUG"
      >|> io.pass_message "Cabs -> Ail completed!"
          (* NOTE: if the debug level is lower the do the printing after the typing *)
      >|> whenM (conf.debug_level > 4 && List.mem Ail conf.astprints) begin
            fun () -> io.run_pp None (Pp_ail_ast.pp_program ail_prog)
          end
      >|> whenM (conf.debug_level > 4 && List.mem Ail conf.pprints) begin
            fun () -> io.run_pp (wrap_fout (Some (filename, "ail"))) (Pp_ail.pp_program ail_prog)
          end
      >>= fun () -> return (sym_suppl, ail_prog) in
  (* -- *)
  let ail_typechecking ail_prog =
    ErrorMonad.to_exception (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
      (GenTyping.annotate_program ail_prog) >>= fun (ailtau_prog, _) ->
    whenM (conf.debug_level <= 4 && List.mem Ail conf.astprints) begin
      fun () ->
        let doc = if conf.debug_level = 4 then
          (* (for debug 4) pretty-printing Ail with type annotations *)
          Pp_ail_ast.pp_program_with_annot ailtau_prog
        else
          Pp_ail_ast.pp_program ailtau_prog in
        io.run_pp None doc
    end >>= fun () ->
    whenM (conf.debug_level <= 4 && List.mem Ail conf.pprints) begin
      fun () ->
        let doc = if conf.debug_level = 4 then
          (* (for debug 4) pretty-printing Ail with type annotations *)
          Pp_ail.pp_program_with_annot ailtau_prog
        else
          Pp_ail.pp_program ailtau_prog in
        io.run_pp (wrap_fout (Some (filename, "ail"))) doc
    end >>= fun () -> return ailtau_prog in
  (* -- *)
  io.print_debug 2 (fun () -> "Using the C frontend") >>= fun () ->
  let processed_filename = Filename.(temp_file (basename filename) "") in
  io.print_debug 5 (fun () -> "C prepocessor outputed in: `" ^ processed_filename ^ "`") >>= fun () ->
  if Sys.command (conf.cpp_cmd ^ " " ^ filename ^ " 1> " ^ processed_filename (*^ " 2> /dev/null"*)) <> 0 then
    error "the C preprocessor failed";
  (* -- *)
  parse processed_filename  >>= fun cabs_tunit            ->
  desugar cabs_tunit        >>= fun (sym_suppl, ail_prog) ->
  ail_typechecking ail_prog >>= fun ailtau_prog           ->
  (* NOTE: the elaboration sets the struct/union tag definitions, so to allow the frontend to be
     used more than once, we need to do reset here *)
  (* TODO(someday): find a better way *)
  Tags.reset_tagDefs ();
  let (sym_suppl', core_file) =
    Translation.translate conf.core_stdlib conf.core_impl (sym_suppl, ailtau_prog) in
  io.set_progress "ELABO" >>= fun () ->
  io.pass_message "Translation to Core completed!" >>= fun () ->
  return (Some cabs_tunit, Some ailtau_prog, sym_suppl', core_file)


let core_frontend (conf, io) ~filename =
  io.print_debug 2 (fun () -> "Using the Core frontend") >>= fun () ->
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser =
    Parser_util.Make (struct
      include Core_parser.Make (struct
        let sym_counter = sym_counter
        let mode = Core_parser_util.ImplORFileMode
        let std = List.fold_left (fun acc (fsym, _) ->
          match fsym with
            | Symbol.Symbol (_, Some str) ->
                let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
                Pmap.add (str, (std_pos, std_pos)) fsym acc
            | Symbol.Symbol (_, None) ->
                acc
        ) (Pmap.empty Core_parser_util._sym_compare) (Pmap.bindings_list (snd conf.core_stdlib))
      end)
      type result = Core_parser_util.result
    end) (Lexer_util.Make (Core_lexer)) in
  Core_parser.parse (Input.file filename) >>= function
    | Core_parser_util.Rfile (sym_main, globs, funs) ->
        Exception.except_return
          ( None
          , None
          , Symbol.Symbol (!sym_counter, None)
          , { Core.main= Some sym_main;
              Core.tagDefs= (Pmap.empty (Symbol.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method));
              Core.stdlib= snd conf.core_stdlib;
              Core.impl= conf.core_impl;
              Core.globs= globs;
              Core.funs= funs } )
    | Core_parser_util.Rstd _ ->
        error "found no `main' function in the Core program"
    | Core_parser_util.Rimpl _ ->
        error "core_frontend found a Rimpl"


let rewrite_core (conf, io) core_file =
  return (Core_rewrite.rewrite_file core_file) >|>
  whenM (conf.debug_level >= 6 && List.mem Core conf.astprints) begin
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


let core_passes (conf, io) ~filename core_file =
  let wrap_fout z = if List.mem FOut conf.ppflags then z else None in
  let module Param_pp_core = Pp_core.Make(struct
    let show_std = List.mem Annot conf.ppflags
    let show_location = List.mem Annot conf.ppflags
    let show_proc_decl = false
  end) in
  whenM conf.typecheck_core begin
    fun () ->
      Core_typing.typecheck_program core_file >>= fun _ ->
      io.pass_message "Core typechecking completed!"
  end >>= fun () ->
  (* TODO: for now assuming a single order comes from indet expressions *)
   begin
    if conf.rewrite_core then
      Core_indet.hackish_order <$> rewrite_core (conf, io) core_file
    else
      return core_file
  end >>= fun core_file' ->
  (* NOTE: unlike the earlier call, this is typechecking after the rewriting and
     the indet passes *)
  Core_typing.typecheck_program core_file' >>= fun typed_core_file' ->
  let typed_core_file'' =
    if conf.sequentialise_core then
      Core_sequentialise.sequentialise_file typed_core_file'
    else
      typed_core_file' in
  whenM (List.mem Core conf.astprints) begin
    fun () ->
      io.run_pp (wrap_fout (Some (filename, "core"))) (Ast_core.ast_file typed_core_file'')
  end >>= fun () ->
  whenM (List.mem Core conf.pprints) begin
    fun () ->
      io.run_pp (wrap_fout (Some (filename, "core"))) (Param_pp_core.pp_file typed_core_file'')
  end >>= fun () -> return (core_file', typed_core_file'')


let interp_backend io sym_suppl core_file ~args ~do_batch ~concurrency ~experimental_unseq exec_mode =
  let module D = Exhaustive_driver in
  let conf = {D.concurrency; experimental_unseq; exec_mode=exec_mode } in
  (* TODO: temporary hack for the command name *)
  if do_batch then begin
    let executions = D.batch_drive sym_suppl core_file ("cmdname" :: args) conf in
    return (Either.Left executions)
  end else
    let open Core in
    D.drive sym_suppl core_file ("cmdname" :: args) conf >>= function
      | (Vloaded (LVspecified (OVinteger ival)) :: _) ->
          (* TODO: yuck *)
          return (Either.Right begin try
            int_of_string (String_mem.string_pretty_of_integer_value ival)
          with | _ ->
            Debug_ocaml.warn [] (fun () -> "Return value was not a (simple) specified integer");
            0
          end)
      | (cval :: _) ->
          io.warn (fun () -> "HELLO> " ^ String_core.string_of_value cval) >>= fun () ->
          return (Either.Right 0)
      | [] ->
          io.warn (fun () -> "BACKEND FOUND EMPTY RESULT") >>= fun () ->
          return (Either.Right 0)


let ocaml_backend (conf, io) ~filename ~ocaml_corestd sym_suppl core_file =
  (* the OCaml backend really needs things to have been sequentialised *)
  (fun (_, typed_core) ->
     if conf.sequentialise_core then typed_core
     else Core_sequentialise.sequentialise_file typed_core)
  <$> core_passes (conf, io) filename core_file
  >>= Codegen_ocaml.gen filename ocaml_corestd sym_suppl


