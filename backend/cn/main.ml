module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline
open Setup


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
  let@ (_, ail_prog_opt, prog0) = c_frontend (conf incl_dirs astprints, io) (stdlib, impl) ~filename in
  let _, (_, ail_prog) = Option.get ail_prog_opt in
  Tags.set_tagDefs prog0.Core.tagDefs;
  let prog1 = Remove_unspecs.rewrite_file prog0 in
  let prog2 = Core_peval.rewrite_file prog1 in
  let prog3 = Milicore.core_to_micore__file Locations.update prog2 in
  let prog4 = Milicore_label_inline.rewrite_file prog3 in
  let statement_locs = CStatements.search ail_prog in
  print_log_file ("original", CORE prog0);
  print_log_file ("without_unspec", CORE prog1);
  print_log_file ("after_peval", CORE prog2);
  return (prog4, ail_prog, statement_locs)


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
  Check.InferenceEqs.use_model_eqs := not no_model_eqs;
  Check.only := only;
  Diagnostics.diag_string := diag;
  check_input_file filename;
  let (prog4, ail_prog, statement_locs) = 
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
         let@ prog5 = Core_to_mucore.normalise_file ail_prog prog4 in
         print_log_file ("mucore", MUCORE prog5);
         Typing.run Context.empty (Check.check prog5 statement_locs lemmata)
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

(* copy-pasting from backend/driver/main.ml *)
let astprints =
  let doc = "Pretty print the intermediate syntax tree for the listed languages \
             (ranging over {cabs, ail})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)


let () =
  let open Term in
  let check_t = 
    pure main $ 
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
      astprints
  in
  Term.exit @@ Term.eval (check_t, Term.info "cn")
