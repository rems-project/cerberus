module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline

module CA=CF.Core_anormalise
module CA_ = CA.Make(Locations)
module Milicore = CF.Milicore

let (>>=) = CF.Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = CF.Exception.except_return
let (let@) = CF.Exception.except_bind



type core_file = (unit,unit) CF.Core.generic_file
type mu_file = unit Retype.Old.mu_file
type retyped_mu_file = unit Retype.New.mu_file

type file = 
  | CORE of core_file
  | MUCORE of mu_file
  | RETYPED_MUCORE of retyped_mu_file




let io =
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


open Setup



let print_file ?(remove_path = false) filename file =
  match file with
  | CORE file ->
     (* CB.Pipeline.run_pp ~remove_path (Some (filename,"core.ast")) 
      *   (CF.Pp_core_ast.pp_file file); *)
     Pp.print_file (filename ^ ".core") (CF.Pp_core.All.pp_file file);
  | MUCORE file ->
     (* CB.Pipeline.run_pp ~remove_path (Some (filename,"mucore.ast")) 
      *   (CF.Pp_mucore_ast.pp_file file); *)
     Pp.print_file (filename ^ ".mucore")
       (CF.Pp_mucore.Basic_standard_typ.pp_file None file);
  | RETYPED_MUCORE file ->
     (* CB.Pipeline.run_pp ~remove_path (Some (filename,"mucore.ast")) 
      *   (CF.Pp_mucore_ast.pp_file file); *)
     Pp.print_file (filename ^ ".mucore")
       (Check.PP_MUCORE.pp_file None file);


module Log : sig 
  val print_log_file : string -> file -> unit
end = struct
  let print_count = ref 0
  let print_log_file filename file =
    if !Debug_ocaml.debug_level > 0 then 
      begin
        Colour.do_colour := false;
        let count = !print_count in
        let file_path = 
          (Filename.get_temp_dir_name ()) ^ 
            Filename.dir_sep ^
            (string_of_int count ^ "__" ^ filename)
        in
        print_file file_path file;
        print_count := 1 + !print_count;
        Colour.do_colour := true;
      end
end

open Log


type rewrite = core_file -> (core_file, CF.Errors.error) CF.Exception.exceptM
type named_rewrite = string * rewrite




let frontend filename =

  Global_ocaml.(set_cerb_conf false Random false Basic false false false false);
  CF.Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->

  c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (_,ail_program_opt,core_file) ->
  CF.Tags.set_tagDefs core_file.CF.Core.tagDefs;
  print_log_file "original" (CORE core_file);

  let core_file = CF.Remove_unspecs.rewrite_file core_file in
  let () = print_log_file "after_remove_unspecified" (CORE core_file) in

  let core_file = CF.Core_peval.rewrite_file core_file in
  let () = print_log_file "after_partial_evaluation" (CORE core_file) in

  let core_file = CF.Core_remove_unused_functions.remove_unused_functions true core_file in
  let () = print_log_file "after_removing_unused_functions" (CORE core_file) in

  let core_file = CF.Core_indet.hackish_order core_file in
  let () = print_log_file "after_hackish_order" (CORE core_file) in

  let@ core_file = CF.Core_typing.typecheck_program core_file in
  let core_file = CF.Core_sequentialise.sequentialise_file core_file in
  let core_file = CB.Pipeline.untype_file core_file in
  let () = print_log_file "after_sequentialisation" (CORE core_file) in

  let mi_file = Milicore.core_to_micore__file CA_.update_loc core_file in
  let mu_file = CA_.normalise_file mi_file in
  print_log_file "after_anf" (MUCORE mu_file);

  let mu_file = CF.Mucore_label_inline.ib_file mu_file in
  print_log_file "after_inlining_break" (MUCORE mu_file);
  
  let pred_defs =
    begin match ail_program_opt with
    | None ->
        assert false
    | Some (_, sigm) ->
        let open Effectful.Make(Resultat) in
        match CompilePredicates.translate mu_file.mu_tagDefs sigm.CF.AilSyntax.cn_predicates with
        | Result.Error err -> CompilePredicates.report_error err; exit 1
        | Result.Ok xs -> xs
    end in

  return (pred_defs, mu_file)




let check_input_file filename = 
  if not (Sys.file_exists filename) then
    CF.Pp_errors.fatal ("file \""^filename^"\" does not exist")
  else if not (String.equal (Filename.extension filename) ".c") then
    CF.Pp_errors.fatal ("file \""^filename^"\" has wrong file extension")



let main 
      filename 
      loc_pp 
      debug_level 
      print_level 
      json 
      state_file 
      no_reorder_points
      no_additional_sat_check
      no_model_eqs
      skip_consistency
      only
      csv_times
      log_times
  =
  if json then begin
      if debug_level > 0 then
        CF.Pp_errors.fatal ("debug level must be 0 for json output");
      if print_level > 0 then
        CF.Pp_errors.fatal ("print level must be 0 for json output");
    end;
  Debug_ocaml.debug_level := debug_level;
  WellTyped.check_consistency := not skip_consistency;
  Pp.loc_pp := loc_pp;
  Pp.print_level := print_level;
  Check.ResourceInference.reorder_points := not no_reorder_points;
  Check.ResourceInference.additional_sat_check := not no_additional_sat_check;
  Check.InferenceEqs.use_model_eqs := not no_model_eqs;
  Check.only := only;
  check_input_file filename;
  Pp.progress_simple "pre-processing" "translating C code";
  begin match frontend filename with
  | CF.Exception.Exception err ->
     prerr_endline (CF.Pp_errors.to_string err); exit 2
  | CF.Exception.Result (pred_defs, file) ->
     try
       let open Resultat in
       Debug_ocaml.maybe_open_csv_timing_file ();
       Pp.maybe_open_times_channel (match (csv_times, log_times) with
         | (Some times, _) -> Some (times, "csv")
         | (_, Some times) -> Some (times, "log")
         | _ -> None);
       let result = 
         Pp.progress_simple "pre-processing" "translating specifications";
         let@ file = Retype.retype_file pred_defs file in
         Typing.run Context.empty (Check.check file)
       in
       Pp.maybe_close_times_channel ();
       match result with
       | Ok () -> exit 0
       | Error e when json -> TypeErrors.report_json ?state_file e; exit 1
       | Error e -> TypeErrors.report ?state_file e; exit 1
     with
     | exc -> 
        Debug_ocaml.maybe_close_csv_timing_file ();
        Pp.maybe_close_times_channel ();
        Printexc.raise_with_backtrace exc (Printexc.get_raw_backtrace ())
  end


open Cmdliner


(* some of these stolen from backend/driver *)
let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let loc_pp =
  let doc = "Print pointer values as hexadecimal or as decimal values (hex | dec)" in
  Arg.(value & opt (enum ["hex", Pp.Hex; "dec", Pp.Dec]) !Pp.loc_pp &
       info ["locs"] ~docv:"HEX" ~doc)

let debug_level =
  let doc = "Set the debug message level for cerberus to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let print_level =
  let doc = "Set the debug message level for the type system to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["p"; "print-level"] ~docv:"N" ~doc)


let json =
  let doc = "output in json format" in
  Arg.(value & flag & info["json"] ~doc)


let state_file =
  let doc = "file in which to output the state" in
  Arg.(value & opt (some string) None & info ["state-file"] ~docv:"FILE" ~doc)

let skip_consistency = 
  let doc = "Skip check for logical consistency of function specifications." in
  Arg.(value & flag & info["skip_consistency"] ~doc)

let no_reorder_points =
  let doc = "Deactivate 'reorder points' optimisation in resource inference." in
  Arg.(value & flag & info["no_reorder_points"] ~doc)

let no_additional_sat_check =
  let doc = "Deactivate 'additional sat check' in inference of q-points." in
  Arg.(value & flag & info["no_additional_sat_check"] ~doc)

let no_model_eqs =
  let doc = "Deactivate 'model based eqs' optimisation in resource inference spine judgement." in
  Arg.(value & flag & info["no_model_eqs"] ~doc)

let csv_times =
  let doc = "file in which to output csv timing information" in
  Arg.(value & opt (some string) None & info ["times"] ~docv:"FILE" ~doc)

let log_times =
  let doc = "file in which to output hierarchical timing information" in
  Arg.(value & opt (some string) None & info ["log_times"] ~docv:"FILE" ~doc)

let only =
  let doc = "only type-check this function" in
  Arg.(value & opt (some string) None & info ["only"] ~doc)


let () =
  let open Term in
  let check_t = 
    pure main $ 
      file $ 
      loc_pp $ 
      debug_level $ 
      print_level $
      json $
      state_file $
      no_reorder_points $
      no_additional_sat_check $
      no_model_eqs $
      skip_consistency $
      only $
      csv_times $
      log_times
  in
  Term.exit @@ Term.eval (check_t, Term.info "cn")
