open Global_ocaml
open Core

open Pp_run

module ND  = Nondeterminism
module SEU = State_exception_undefined

let (>>=) = SEU.stExceptUndef_bind

let isActive = function
  | (ND.Active _, _, _) ->
      true
  | _ ->
      false

type driver_conf = {
(* TODO: bring back ==> [`Interactive | `Exhaustive | `Random] -> *)
  exec_mode: Smt2.execution_mode;
  concurrency: bool;
  experimental_unseq: bool;
  fs_dump: bool;
}

type execution_result = (Core.value list, Errors.error) Exception.exceptM


let string_of_driver_error = function
  | Driver.DErr_core_run err ->
      Pp_errors.string_of_core_run_cause err
  | Driver.DErr_memory err ->
      Mem_common.instance_Show_Show_Mem_common_mem_error_dict.Lem_pervasives.show_method err
  | Driver.DErr_concurrency str ->
      "Concurrency error: " ^ str
  | Driver.DErr_other str ->
      str


(* TODO: make the output match the json format from charon2 (or at least add a option for that) *)
let batch_drive mode (file: 'a Core.file) args fs_state conf : string list =
  Random.self_init ();
  
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run_aux.convert_file file in
  
  (* computing the value (or values if exhaustive) *)
  let initial_dr_st = Driver.initial_driver_state file fs_state in
  let values = Smt2.runND conf.exec_mode Ocaml_mem.cs_module (Driver.drive conf.concurrency conf.experimental_unseq file args) initial_dr_st in  
  let is_charon = match mode with
    | `Batch       -> false
    | `CharonBatch -> true in
  let has_multiple =
    List.length values > 1 in
  
  List.mapi (fun i (res, z3_strs, nd_st) ->
    let (exit, result) = begin match res with
      | ND.Active dres ->
          let str_v = String_core.string_of_value dres.Driver.dres_core_value in
          if is_charon then
            (" (exit = "^ str_v ^ ")", dres.Driver.dres_stdout)
          else
            ("", "Defined {value: \"" ^ str_v ^ "\", stdout: \"" ^ String.escaped dres.Driver.dres_stdout ^
            "\", blocked: \"" ^ if dres.Driver.dres_blocked then "true\"}" else "false\"}\n")
      | ND.Killed (ND.Undef0 (loc, [])) ->
          (* TODO: this is probably an error *)
          begin
            ("", "Undefined behaviour: [empty UB, probably a cerberus BUG] at " ^
            Location_ocaml.location_to_string ~charon:is_charon loc ^ "\n")
          end
      | ND.Killed (ND.Undef0 (loc, ub::_)) ->
          begin
            ("", "Undefined behaviour: " ^ Undefined.ub_short_string ub ^ " at " ^
            Location_ocaml.location_to_string ~charon:is_charon loc ^ "\n")
          end
      | ND.Killed (ND.Error0 (_, str)) ->
          begin
            ("", "Error {msg: " ^ str ^ "}\n")
          end
      | ND.Killed (ND.Other dr_err) ->
          begin
            ("", "Killed {msg: " ^ string_of_driver_error dr_err ^ "}\n")
          end
    end in
    let constraints =
      if !Debug_ocaml.debug_level > 0 then begin
        match z3_strs with
          | [] ->
              "EMPTY CONSTRAINTS\n"
          | _ ->
              Colour.(do_colour:=true; ansi_format [Blue] (String.concat "\n" z3_strs))
              |> Printf.sprintf "BEGIN CONSTRAINTS%sEND CONSTRAINTS\n"
      end else ""
    in
    if has_multiple then
      (if i>0 then "\n" else "") ^ Printf.sprintf "EXECUTION %d%s:\n%s%s" i exit constraints result
    else
      constraints ^ result
  ) values


let drive file args fs_state conf : execution_result =
  Random.self_init ();
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run_aux.convert_file file in
  (* computing the value (or values if exhaustive) *)
  let initial_dr_st = Driver.initial_driver_state file fs_state in
  let values = Smt2.runND conf.exec_mode Ocaml_mem.cs_module
      (Driver.drive conf.concurrency conf.experimental_unseq file args) initial_dr_st in
  let n_actives = List.length (List.filter isActive values) in
  let n_execs   = List.length values                        in
  Debug_ocaml.print_debug 1 [] (fun () ->
    Printf.sprintf "Number of executions: %d actives (%d killed)\n" n_actives (n_execs - n_actives)
  );
  if n_actives = 0 then begin
    print_endline Colour.(ansi_format [Red]
      (Printf.sprintf "FOUND NO ACTIVE EXECUTION (with %d killed)\n" (n_execs - n_actives))
    );
    List.iteri (fun n exec ->
      match exec with
        | (ND.Active _, _, _) ->
            assert false
        | (ND.Killed reason, z3_strs, st) ->
          (*
            let reason_str = match reason with
              | ND.Undef0 (loc, ubs) ->
                  "undefined behaviour[" ^ Location_ocaml.location_to_string loc ^ "]: "
                  ^ Lem_show.stringFromList Undefined.stringFromUndefined_behaviour ubs
              | ND.Error0 (loc , str) ->
                  "static error[" ^ Location_ocaml.location_to_string loc ^ "]: " ^ str
              | ND.Other str ->
                  string_of_driver_error str in
             *)
            begin
(*
      if reason_str = "reached unsatisfiable constraints" then
      print_endline Colour.(ansi_format [Red] 
        (Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_old_constraints st.ND.eqs) (String.concat "\n" (List.rev (Dlist.toList st.ND.log))))
      )
else
        Debug_ocaml.print_debug 2 [] (fun () -> Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_old_constraints st.ND.eqs) (String.concat "\n" (List.rev (Dlist.toList st.ND.log))))
*)
            end
    ) values
  end;
  
  let ky  = ref [] in
  let ret = ref [] in
  
  List.iteri (fun n exec ->
    match exec with
      | (ND.Active dres (* (stdout, (is_blocked, conc_st, cval), (dr_steps, coreRun_steps)) *), z3_strs, st) ->
          let str_v = String_core.string_of_value dres.Driver.dres_core_value in
          let str_v_ = str_v ^ dres.Driver.dres_stdout in
          if true (* not (List.mem str_v_ !ky) *) then (
            if Debug_ocaml.get_debug_level () = 0 then
              (print_string dres.Driver.dres_stdout; flush_all());
            
            Debug_ocaml.print_debug 1 [] (fun () ->
(*              Printf.sprintf "\n\n\n\n\nExecution #%d (value = %s) under constraints:\n=====\n%s\n=====\n" n str_v (Pp_cmm.pp_old_constraints st.ND.eqs) ^*)
              Printf.sprintf "BEGIN stdout\n%s\nEND stdout\n" dres.Driver.dres_stdout ^
              Printf.sprintf "driver steps: %d\n" dres.Driver.dres_driver_steps (* ^ 
              Printf.sprintf "BEGIN LOG\n%s\nEND LOG" (String.concat "\n" (List.rev (List.map (fun z -> "LOG ==> " ^ z) (Dlist.toList st.ND.log)))) *)

(* ^
              Printf.sprintf "BEGIN LOG\n%s\nEND LOG\n" (String.concat "\n" (List.rev (Dlist.toList log))) *)
            );
          );
          if not (List.mem str_v_ !ky) && not dres.Driver.dres_blocked then (
(*
            if conf.concurrency then
              Debug_ocaml.print_debug 2 [] (fun () -> Pp_cmm.dot_of_exeState conc_st str_v (Pp_cmm.pp_old_constraints st.ND.eqs)); *)
            
            ky := str_v_ :: !ky;
            ret := dres.Driver.dres_core_value :: !ret;
        ) else
          Debug_ocaml.print_debug 4 [] (fun () ->
            "SKIPPING: " ^ if dres.Driver.dres_blocked then "(blocked)" else "" ^
            "eqs= " ^ "Pp_cmm.pp_old_constraints st.ND.eqs"
          );
        if conf.fs_dump then begin
          print_endline "File System:";
          print_endline @@ Sexplib.Sexp.to_string_hum @@ Sibylfs.sexp_of_fs_state st.Driver.fs_state
        end

      | (ND.Killed (ND.Undef0 (loc, ubs)), _, _) ->
          prerr_endline (Pp_errors.to_string (loc, Errors.(DRIVER (Driver_UB ubs))))

     (*
          let str_v = Location_ocaml.location_to_string loc ^
            (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs)) in
          
          if not (List.mem str_v !ky) then (
            print_endline (
              Colour.(ansi_format [Red] ("UNDEFINED BEHAVIOUR[" ^ Location_ocaml.location_to_string loc ^ "]:\n" ^
                (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs))
              ))
           );
            ky := str_v :: !ky;
          ) else
            ()
        *)
      
      | (ND.Killed (ND.Error0 (loc, str)), _, _) ->
          print_endline (Colour.(ansi_format [Red] ("IMPL-DEFINED STATIC ERROR[" ^ Location_ocaml.location_to_string loc ^ "]: " ^ str)))
      
      | (ND.Killed (ND.Other reason), _, st) ->
          print_endline (Colour.(ansi_format [Red] ("OTHER ERROR: " ^ string_of_driver_error reason)))
  ) values;
  Exception.except_return !ret
