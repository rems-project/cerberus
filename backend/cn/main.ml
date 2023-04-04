open Builtins
module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline
open Setup
open CF.Cn


let return = CF.Exception.except_return
let (let@) = CF.Exception.except_bind



type core_file = (unit,unit) CF.Core.generic_file
type mu_file = unit Mucore.mu_file


type file = 
  | CORE of core_file
  | MUCORE of mu_file



let print_file filename file =
  match file with
  | CORE file ->
     Pp.print_file (filename ^ ".core") (CF.Pp_core.All.pp_file file);
  | MUCORE file ->
     Pp.print_file (filename ^ ".mucore")
       (Pp_mucore.Basic.pp_file None file);


module Log : sig 
  val print_log_file : (string * file) -> unit
end = struct
  let print_count = ref 0
  let print_log_file (filename, file) =
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






let frontend incl_dirs astprints filename state_file =
  let open CF in
  Global_ocaml.set_cerb_conf "Cn" false Random false Basic false false false false;
  Ocaml_implementation.set Ocaml_implementation.HafniumImpl.impl;
  Switches.set ["inner_arg_temps"];
  let@ stdlib = load_core_stdlib () in
  let@ impl = load_core_impl stdlib impl_name in
  let@ (_, ail_prog_opt, prog0) = c_frontend ~cnnames:cn_builtin_fun_names (conf incl_dirs astprints, io) (stdlib, impl) ~filename in
  let markers_env, (_, ail_prog) = Option.get ail_prog_opt in
  Tags.set_tagDefs prog0.Core.tagDefs;
  let prog1 = Remove_unspecs.rewrite_file prog0 in
  let prog2 = Core_peval.rewrite_file prog1 in
  let prog3 = Milicore.core_to_micore__file Locations.update prog2 in
  let prog4 = Milicore_label_inline.rewrite_file prog3 in
  let statement_locs = CStatements.search ail_prog in
  print_log_file ("original", CORE prog0);
  print_log_file ("without_unspec", CORE prog1);
  print_log_file ("after_peval", CORE prog2);
  return (prog4, (markers_env, ail_prog), statement_locs)


let handle_frontend_error = function
  | CF.Exception.Exception err ->
     prerr_endline (CF.Pp_errors.to_string err); exit 2
  | CF.Exception.Result result ->
     result





let check_input_file filename = 
  if not (Sys.file_exists filename) then
    CF.Pp_errors.fatal ("file \""^filename^"\" does not exist")
  else if not (String.equal (Filename.extension filename) ".c") then
    CF.Pp_errors.fatal ("file \""^filename^"\" has wrong file extension")



(* Executable spec helper functions *)

type executable_spec = {
    pre_post: (CF.Symbol.sym * (string * string)) list;
    in_stmt: (Location_ocaml.t * string) list;
}

let empty_executable_spec = {
    pre_post = [];
    in_stmt = [];
}


  
let generate_c_assertion cn_assertion =
  match cn_assertion with
  | CN_assert_exp e_ -> String.concat "" ["assert("; Cn_to_ail.(pp_ail (cn_to_ail_expr e_)); ");"]
  | _ -> "" (* TODO: CN_assert_qexp *)
  

let generate_c_statements cn_statements =
  let generate_c_statement (CN_statement (loc, stmt_)) = 
    let pp_statement =
      match stmt_ with
      | CN_assert_stmt e -> generate_c_assertion e
      | _ -> ""
    in 
  (loc, pp_statement)
  in
  List.map generate_c_statement cn_statements


(* Core_to_mucore.instrumentation list -> executable_spec *)
let generate_c_specs instrumentation_list =
  let open Core_to_mucore in
  let generate_c_spec instrumentation =
    ([], generate_c_statements instrumentation.statements)
  in
  let specs = List.map generate_c_spec instrumentation_list in 
  let (pre_post, in_stmt) = List.split specs in
  let pre_post = List.fold_left List.append [] pre_post in
  let in_stmt = List.fold_left List.append [] in_stmt in
  let executable_spec = {pre_post = pre_post; in_stmt = in_stmt} in
  executable_spec





let main 
      filename 
      incl_dirs
      loc_pp 
      debug_level 
      print_level 
      no_timestamps
      json 
      state_file 
      diag
      lemmata
      no_reorder_points
      no_additional_sat_check
      no_model_eqs
      only
      csv_times
      log_times
      random_seed
      output_decorated
      astprints
  =
  if json then begin
      if debug_level > 0 then
        CF.Pp_errors.fatal ("debug level must be 0 for json output");
      if print_level > 0 then
        CF.Pp_errors.fatal ("print level must be 0 for json output");
    end;
  Debug_ocaml.debug_level := debug_level;
  Pp.loc_pp := loc_pp;
  Pp.print_level := print_level;
  Pp.print_timestamps := not no_timestamps;
  Solver.random_seed := random_seed;
  ResourceInference.reorder_points := not no_reorder_points;
  ResourceInference.additional_sat_check := not no_additional_sat_check;
  Check.use_model_eqs := not no_model_eqs;
  Check.only := only;
  Diagnostics.diag_string := diag;
  check_input_file filename;
  let (prog4, (markers_env, ail_prog), statement_locs) = 
    handle_frontend_error 
      (frontend incl_dirs astprints filename state_file)
  in
  Debug_ocaml.maybe_open_csv_timing_file ();
  Pp.maybe_open_times_channel 
    (match (csv_times, log_times) with
     | (Some times, _) -> Some (times, "csv")
     | (_, Some times) -> Some (times, "log")
     | _ -> None);
  try begin
      let result = 
        let open Resultat in
         let@ prog5 = Core_to_mucore.normalise_file (markers_env, ail_prog) prog4 in
         let instrumentation = Core_to_mucore.collect_instrumentation prog5 in
         print_log_file ("mucore", MUCORE prog5);
         let@ res = Typing.run Context.empty (Check.check prog5 statement_locs lemmata) in
         begin match output_decorated with
         | None -> ()
         | Some output_filename ->
            let oc = Stdlib.open_out output_filename in
            (* TODO(Rini): example for how to use Source_injection.get_magics_of_statement *)
            (* List.iter (fun (_, (_, _, _, _, stmt)) ->
              List.iteri(fun i xs ->
                List.iteri (fun j (loc, str) ->
                  Printf.fprintf stderr "[%d] [%d] ==> %s -- '%s'\n"
                  i j (Location_ocaml.simple_location loc) (String.escaped str)
                ) xs
              ) (Source_injection.get_magics_of_statement stmt)
            ) ail_prog.function_definitions; *)
            (* let extracted_statements = List.map (fun (_, (_, _, _, _, stmt)) -> stmt) ail_prog.function_definitions in
            let magic_statements = List.map Source_injection.get_magics_of_statement extracted_statements in
            let magic_statements_reduced = List.fold_left List.append [] (List.fold_left List.append [] magic_statements)  *)
            (* in *)
            let executable_spec = generate_c_specs instrumentation in
            begin match
              Source_injection.(output_injections oc
                { filename; sigm= ail_prog
                ; pre_post=executable_spec.pre_post
                ; in_stmt=executable_spec.in_stmt}
              )
            with
            | Ok () ->
                ()
            | Error str ->
                (* TODO(Christopher/Rini): maybe lift this error to the exception monad? *)
                prerr_endline str
            end
         end;
         return res
       in
       Pp.maybe_close_times_channel ();
       match result with
       | Ok () -> exit 0
       | Error e when json -> TypeErrors.report_json ?state_file e; exit 1
       | Error e -> TypeErrors.report ?state_file e; exit 1
     end 
     with
     | exc -> 
        Debug_ocaml.maybe_close_csv_timing_file ();
        Pp.maybe_close_times_channel ();
        Printexc.raise_with_backtrace exc (Printexc.get_raw_backtrace ())



open Cmdliner


(* some of these stolen from backend/driver *)
let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let incl_dir =
  let doc = "Add the specified directory to the search path for the\
             C preprocessor." in
  Arg.(value & opt_all dir [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let loc_pp =
  let doc = "Print pointer values as hexadecimal or as decimal values (hex | dec)" in
  Arg.(value & opt (enum ["hex", Pp.Hex; "dec", Pp.Dec]) !Pp.loc_pp &
       info ["locs"] ~docv:"HEX" ~doc)

let debug_level =
  let doc = "Set the debug message level for cerberus to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let print_level =
  let doc = "Set the debug message level for the type system to $(docv) (should range over [0-15])." in
  Arg.(value & opt int 0 & info ["p"; "print-level"] ~docv:"N" ~doc)

let no_timestamps =
  let doc = "Disable timestamps in print-level debug messages"
 in
  Arg.(value & flag & info ["no_timestamps"] ~doc)


let json =
  let doc = "output in json format" in
  Arg.(value & flag & info["json"] ~doc)


let state_file =
  let doc = "file in which to output the state" in
  Arg.(value & opt (some string) None & info ["state-file"] ~docv:"FILE" ~doc)

let diag =
  let doc = "explore branching diagnostics with key string" in
  Arg.(value & opt (some string) None & info ["diag"] ~doc)

let lemmata =
  let doc = "lemmata generation mode (target filename)" in
  Arg.(value & opt (some string) None & info ["lemmata"] ~docv:"FILE" ~doc)

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

let random_seed =
  let doc = "Set the SMT solver random seed (default 1)." in
  Arg.(value & opt int 0 & info ["r"; "random-seed"] ~docv:"I" ~doc)

let only =
  let doc = "only type-check this function" in
  Arg.(value & opt (some string) None & info ["only"] ~doc)

(* TODO(Christopher/Rini): I'm adding a tentative cli option, rename/change it to whatever you prefer *)
let output_decorated =
  let doc = "output a version of the translation unit decorated with C runtime translations of the CN annotations" in
  Arg.(value & opt (some string) None & info ["output_decorated"] ~docv:"FILE" ~doc)

(* copy-pasting from backend/driver/main.ml *)
let astprints =
  let doc = "Pretty print the intermediate syntax tree for the listed languages \
             (ranging over {cabs, ail, core, types})." in
  Arg.(value & opt (list (enum [("cabs", Cabs); ("ail", Ail); ("core", Core); ("types", Types)])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)


let () =
  let open Term in
  let check_t = 
    const main $ 
      file $ 
      incl_dir $
      loc_pp $ 
      debug_level $ 
      print_level $
      no_timestamps $
      json $
      state_file $
      diag $
      lemmata $
      no_reorder_points $
      no_additional_sat_check $
      no_model_eqs $
      only $
      csv_times $
      log_times $
      random_seed $
      output_decorated $
      astprints
  in
  Stdlib.exit @@ Cmd.(eval (v (info "cn") check_t))
