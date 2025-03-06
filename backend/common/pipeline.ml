open Cerb_frontend
open Cerb_global

(* Pipeline *)

let (>>=) = Exception.except_bind
(*let (>>) m f = m >>= fun _ -> f*)
let (<$>)  = Exception.except_fmap
let return = Exception.except_return

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
  Filename.concat (Cerb_runtime.runtime ()) "libcore"

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
    | Exception.Result (Core_parser_util.Rimpl impl_map) ->
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
  pass_message: string -> (unit, Errors.error) Exception.exceptM;
  set_progress: string -> (unit, Errors.error) Exception.exceptM;
  run_pp: string option -> PPrint.document -> (unit, Errors.error) Exception.exceptM;
  print_endline: string -> (unit, Errors.error) Exception.exceptM;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) Exception.exceptM;
  warn: ?always:bool -> (unit -> string) -> (unit, Errors.error) Exception.exceptM;
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
        Exception.fail (Cerb_location.unknown, Errors.CPP (String.concat "\n" err))
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
  (*   match Core_rewrite2.rw_file core_file with
   *   | Exception.Result core_file -> core_file
   *   | Exception.Exception err -> prerr_endline err; failwith "error"
   * in  *)
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


let untype_file (file: 'a Core.typed_file) : 'a Core.file =
  let open Core in
  let untype_ctor = fun ctor -> ctor (* function
     * | Cnil _ ->
     *     Cnil ()
     * | (Ccons as ctor)
     * | (Ctuple as ctor)
     * | (Carray as ctor)
     * | (Civmax as ctor)
     * | (Civmin as ctor)
     * | (Civsizeof as ctor)
     * | (Civalignof as ctor)
     * | (CivCOMPL as ctor)
     * | (CivAND as ctor)
     * | (CivOR as ctor)
     * | (CivXOR as ctor)
     * | (Cspecified as ctor)
     * | (Cunspecified as ctor)
     * | (Cfvfromint as ctor)
     * | (Civfromfloat as ctor) ->
     *     ctor in *)
  in
  let rec untype_pattern (Pattern (annots, pat_)) =
    Pattern ( annots
            , match pat_ with
                | (CaseBase _ as pat_) ->
                    pat_
                | CaseCtor (ctor, pats) ->
                    CaseCtor (untype_ctor ctor, List.map untype_pattern pats) ) in
  let rec untype_pexpr (Pexpr (annots, _, pexpr_) : Core.typed_pexpr) : Core.pexpr =
    let aux = function
      | (PEsym _ as pe)
      | (PEimpl _ as pe)
      | (PEval _ as pe)
      | (PEundef _ as pe) ->
          pe
      | PEerror (str, pe) ->
          PEerror (str, untype_pexpr pe)
      | PEconstrained xs ->
          PEconstrained (List.map (fun (z, pe) -> (z, untype_pexpr pe)) xs)
      | PEctor (ctor, pes) ->
          PEctor (untype_ctor ctor, List.map untype_pexpr pes)
      | PEcase (pe, pat_pes) ->
          PEcase (untype_pexpr pe, List.map (fun (pat, pe) -> (untype_pattern pat, untype_pexpr pe)) pat_pes)
      | PEarray_shift (pe1, ty, pe2) ->
          PEarray_shift (untype_pexpr pe1, ty, untype_pexpr pe2)
      | PEmember_shift (pe1, tag_sym, membr_ident) ->
          PEmember_shift (untype_pexpr pe1, tag_sym, membr_ident)
      | PEmemop (mop, pes) ->
          PEmemop (mop, List.map untype_pexpr pes)
      | PEnot pe ->
          PEnot (untype_pexpr pe)
      | PEop (binop, pe1, pe2) ->
          PEop (binop, untype_pexpr pe1, untype_pexpr pe2)
      | PEconv_int (ity, pe) ->
          PEconv_int (ity, untype_pexpr pe)
      | PEwrapI (ity, iop, pe1, pe2) ->
          PEwrapI (ity, iop, untype_pexpr pe1, untype_pexpr pe2)
      | PEcatch_exceptional_condition (ity, iop, pe1, pe2) ->
          PEcatch_exceptional_condition (ity, iop, untype_pexpr pe1, untype_pexpr pe2)
      | PEstruct (tag_sym, xs) ->
          PEstruct (tag_sym, List.map (fun (z, pe) -> (z, untype_pexpr pe)) xs)
      | PEunion (tag_sym, membr_ident, pe) ->
          PEunion (tag_sym, membr_ident, untype_pexpr pe)
      | PEcfunction pe ->
          PEcfunction (untype_pexpr pe)
      | PEmemberof (tag_sym, membr_ident, pe) ->
          PEmemberof (tag_sym, membr_ident, untype_pexpr pe)
      | PEcall (nm, pes) ->
          PEcall (nm, List.map untype_pexpr pes)
      | PElet (pat, pe1, pe2) ->
          PElet (untype_pattern pat, untype_pexpr pe1, untype_pexpr pe2)
      | PEif (pe1, pe2, pe3) ->
          PEif (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3)
      | PEis_scalar pe ->
          PEis_scalar (untype_pexpr pe)
      | PEis_integer pe ->
          PEis_integer (untype_pexpr pe)
      | PEis_signed pe ->
          PEis_signed (untype_pexpr pe)
      | PEis_unsigned pe ->
          PEis_unsigned (untype_pexpr pe)
      | PEbmc_assume pe ->
          PEbmc_assume (untype_pexpr pe)
      | PEare_compatible (pe1, pe2) ->
          PEare_compatible (untype_pexpr pe1, untype_pexpr pe2)
    in Pexpr (annots, (), aux pexpr_) in
  let untype_action (Action (loc, a, act_)) =
    Action ( loc, a
           , match act_ with
               | Create (pe1, pe2, pref) ->
                   Create (untype_pexpr pe1, untype_pexpr pe2, pref)
               | CreateReadOnly (pe1, pe2, pe3, pref) ->
                   CreateReadOnly (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, pref)
               | Alloc0 (pe1, pe2, pref) ->
                   Alloc0 (untype_pexpr pe1, untype_pexpr pe2, pref)
               | Kill (kind, pe) ->
                   Kill (kind, untype_pexpr pe)
               | Store0 (b, pe1, pe2, pe3, mo) ->
                   Store0 (b, untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, mo)
               | Load0 (pe1, pe2, mo) ->
                   Load0 (untype_pexpr pe1, untype_pexpr pe2, mo)
               | SeqRMW (b, pe1, pe2, sym, pe3) ->
                   SeqRMW (b, untype_pexpr pe1, untype_pexpr pe2, sym, untype_pexpr pe3)
               | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
                   RMW0 (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, untype_pexpr pe4, mo1, mo2)
               | Fence0 mo ->
                   Fence0 mo
               | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
                   CompareExchangeStrong (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, untype_pexpr pe4, mo1, mo2)
               | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
                   CompareExchangeWeak (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, untype_pexpr pe4, mo1, mo2)
               | LinuxFence mo ->
                   LinuxFence mo
               | LinuxLoad (pe1, pe2, mo) ->
                   LinuxLoad (untype_pexpr pe1, untype_pexpr pe2, mo)
               | LinuxStore ( pe1, pe2, pe3, mo) ->
                   LinuxStore ( untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, mo)
               | LinuxRMW (pe1, pe2, pe3, mo) ->
                   LinuxRMW (untype_pexpr pe1, untype_pexpr pe2, untype_pexpr pe3, mo) ) in
  let rec untype_expr (Expr (annots, expr_)) =
    let aux = function
      | Epure pe ->
          Epure (untype_pexpr pe)
      | Ememop (memop, pes) ->
          Ememop (memop, List.map untype_pexpr pes)
      | Eaction (Paction (p, act)) ->
          Eaction (Paction (p, untype_action act))
      | Ecase (pe, xs) ->
          Ecase (untype_pexpr pe, List.map (fun (pat, e) -> (untype_pattern pat, untype_expr e)) xs)
      | Elet (pat, pe1, e2) ->
          Elet (untype_pattern pat, untype_pexpr pe1, untype_expr e2)
      | Eif (pe, e1, e2) ->
          Eif (untype_pexpr pe, untype_expr e1, untype_expr e2)
      | Eccall (a, pe1, pe2, pes) ->
          Eccall (a, untype_pexpr pe1, untype_pexpr pe2, List.map untype_pexpr pes)
      | Eproc (a, nm, pes) ->
          Eproc (a, nm, List.map untype_pexpr pes)
      | Eunseq es ->
          Eunseq (List.map untype_expr es)
      | Ewseq (pat, e1, e2) ->
          Ewseq (untype_pattern pat, untype_expr e1, untype_expr e2)
      | Esseq (pat, e1, e2) ->
          Esseq (untype_pattern pat, untype_expr e1, untype_expr e2)
      | Ebound e ->
          Ebound (untype_expr e)
      | End es ->
          End (List.map untype_expr es)
      | Esave (sym_bTy, xs, e) ->
          Esave (sym_bTy, List.map (fun (sym, (bTy, pe)) -> (sym, (bTy, untype_pexpr pe))) xs, untype_expr e)
      | Erun (a, sym, pes) ->
          Erun (a, sym, List.map untype_pexpr pes)
      | Epar es ->
          Epar (List.map untype_expr es)
      | Ewait tid ->
          Ewait tid
      | Eannot _ | Eexcluded _ ->
          assert false (* only exists during Core runtime *)
    in Expr (annots, aux expr_) in
  let untype_generic_fun_map_decl = function
    | Fun (bty, xs, pe) ->
        Fun (bty, xs, untype_pexpr pe)
    | Proc (loc, mrk, bTy, xs, e) ->
        Proc (loc, mrk, bTy, xs, untype_expr e)
    | ProcDecl _ as decl ->
        decl
    | BuiltinDecl _ as decl ->
        decl in
  let untype_generic_impl_decl = function
    | Def (bTy, pe) ->
        Def (bTy, untype_pexpr pe)
    | IFun (bTy, xs, pe) ->
        IFun (bTy, xs, untype_pexpr pe) in
  let untype_generic_globs = function
    | GlobalDef (bTy, e) ->
        GlobalDef (bTy, untype_expr e)
    | GlobalDecl _ as glob ->
        glob in
  { main= file.main
  ; calling_convention= file.calling_convention
  ; tagDefs= file.tagDefs
  ; stdlib= Pmap.map untype_generic_fun_map_decl file.stdlib
  ; impl= Pmap.map untype_generic_impl_decl file.impl
  ; globs= List.map (fun (sym, z) -> (sym, untype_generic_globs z)) file.globs
  ; funs= Pmap.map untype_generic_fun_map_decl  file.funs
  ; extern= file.extern
  ; funinfo= file.funinfo
  ; loop_attributes0= file.loop_attributes0
  ; visible_objects_env= file.visible_objects_env
 }

let typed_core_passes (conf, io) core_file =
  whenM conf.typecheck_core begin
    fun () ->
      Core_typing.typecheck_program core_file >>= fun _ ->
      io.pass_message "Core typechecking completed!"
  end >>= fun () ->
  (* TODO: for now assuming a single order comes from indet expressions *)
  Core_indet.hackish_order <$> begin
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
  return (untype_file typed_core_file'', typed_core_file'')

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
  let core_file =
    if Switches.(has_switch SW_strict_reads && not (is_CHERI ())) then
      Remove_unspecs.rewrite_file core_file
    else
      core_file in
  Core_indet.hackish_order <$> begin
    if conf.sequentialise_core || conf.typecheck_core then
      typed_core_passes (conf, io) core_file >>= fun (core_file, typed_core_file) ->
      print_core (conf, io) ~filename typed_core_file >>= fun _ ->
      return core_file
    else if conf.rewrite_core then
      core_rewrite (conf, io) core_file >>= print_core (conf, io) ~filename
    else
      print_core (conf, io) ~filename core_file
  end

let interp_backend io core_file ~args ~batch ~fs ~driver_conf =
  let module D = Driver_ocaml in
  let fs_state = match fs with
    | None -> Sibylfs.fs_initial_state
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
      | (Vloaded (LVspecified (OVinteger ival)) :: _) ->
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
  { dump_main: Symbol.sym option;
    dump_calling_convention: Core.calling_convention;
    dump_tagDefs: (Symbol.sym * (Cerb_location.t * Ctype.tag_definition)) list;
    dump_globs: (Symbol.sym * ('a, unit) Core.generic_globs) list;
    dump_funs: (Symbol.sym * (unit, 'a) Core.generic_fun_map_decl) list;
    dump_extern: (Symbol.identifier * (Symbol.sym list * Core.linking_kind)) list;
    dump_funinfo: (Symbol.sym * (Cerb_location.t * Annot.attributes * Ctype.ctype * (Symbol.sym option * Ctype.ctype) list * bool * bool)) list;
    (* dump_loop_attributes: (int * Annot.attributes) list; *)
  }

let sym_compare (Symbol.Symbol (d1, n1, _)) (Symbol.Symbol (d2, n2, _)) =
  if d1 = d2 then compare n1 n2
  else Digest.compare d1 d2

let cabsid_compare (Symbol.Identifier (_, s1)) (Symbol.Identifier (_, s2)) =
  String.compare s1 s2

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
    tagDefs= map_from_assoc sym_compare dump.dump_tagDefs;
    stdlib=  snd core_stdlib;
    impl=    core_impl;
    globs=   dump.dump_globs;
    funs=    map_from_assoc sym_compare dump.dump_funs;
    extern=  map_from_assoc cabsid_compare dump.dump_extern;
    funinfo= map_from_assoc sym_compare dump.dump_funinfo;
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


