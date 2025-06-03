open Cerb_frontend
open Cerb_global

module ND  = Nondeterminism
module SEU = State_exception_undefined

let isActive = function
  | (ND.Active _, _, _) -> true
  | _ -> false

type driver_conf = {
(* TODO: bring back ==> [`Interactive | `Exhaustive | `Random] -> *)
  exec_mode: execution_mode;
  concurrency: bool;
  fs_dump: bool;
  trace: bool;
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

type batch_exit =
  | Unspecified of Ctype.ctype
  | Specified of Z.t
  | OtherValue of Core.value

type batch_output =
  | Defined of { exit: batch_exit; stdout: string; stderr: string; blocked: bool }
  | Undefined of { ub: Undefined.undefined_behaviour; stderr: string; loc: Cerb_location.t }
  | Error of { msg: string; stderr: string; }

let string_of_batch_exit exit =
  let cval =
    let open Core in
    match exit with
      | Unspecified ty ->
        Vloaded (LVunspecified ty)
      | Specified n ->
          Vloaded (LVspecified (OVinteger (Impl_mem.integer_ival n)))
      | OtherValue cval ->
          cval in
  String_core.string_of_value cval

let string_of_batch_output ?(json=false) ?(is_charon=false) i_opt (z3_strs, exec) =
  let buf = Buffer.create 16 in
  let constrs_str =
    if !Cerb_debug.debug_level > 0 then begin
      match z3_strs with
        | [] ->
            "EMPTY CONSTRAINTS\n"
        | _ ->
          Cerb_colour.(without_colour (fun z ->
            ansi_format [Blue] (String.concat "\n" z)
          )) z3_strs
            |> Printf.sprintf "BEGIN CONSTRAINTS\n%s\nEND CONSTRAINTS\n"
      end
    else
      "" in
  let has_multiple =
    match i_opt with
      | Some i ->
          Printf.bprintf buf "EXECUTION %d" i;
          true
      | None ->
          Buffer.add_string buf constrs_str;
          false in
  begin match exec with
    | Defined { exit; stdout; stderr; blocked } ->
        let exit_str = Cerb_colour.without_colour string_of_batch_exit exit in
        if is_charon then begin
          if has_multiple then begin
            Printf.bprintf buf " (exit = %s):\n" exit_str;
            Buffer.add_string buf constrs_str
          end;
          Buffer.add_string buf stdout;
          prerr_string stderr
        end else if json then begin
          Yojson.to_buffer buf begin
            `Assoc [ "status", `String "Defined"
                   ; "details", `Assoc [ "value", `String exit_str
                                       ; "stdout", `String (String.escaped stdout)
                                       ; "stderr", `String (String.escaped stderr) ] ]
          end
        end else begin
          begin if has_multiple then
            Buffer.add_string buf  ":\n"
          end;
          Buffer.add_string buf constrs_str;
          Printf.bprintf buf "Defined {value: \"%s\", stdout: \"%s\", stderr: \"%s\", blocked: \"%s\"}"
            exit_str
            (String.escaped stdout) (String.escaped stderr)
            (if blocked then "true" else "false")
        end
    | Undefined { ub; stderr; loc } ->
        begin if has_multiple then
          Buffer.add_string buf  ":\n"
        end;
        Buffer.add_string buf constrs_str;
        if is_charon then begin
          prerr_string stderr;
          Printf.bprintf buf "Undefined {ub: \"%s\", loc: \"%s\"}%s"
          (Undefined.stringFromUndefined_behaviour ub)
          (Cerb_location.simple_location loc)
          (if is_charon then "\n" else "")
        end else if json then begin
          Yojson.to_buffer buf begin
            `Assoc [ "status", `String "Undefined"
                   ; "details", `Assoc [ "ub", `String (Undefined.stringFromUndefined_behaviour ub)
                                       ; "stderr", `String (String.escaped stderr)
                                       ; "loc", (Cerb_location.to_json loc :> Yojson.t) ] ]
          end
        end else
          Printf.bprintf buf "Undefined {ub: \"%s\", stderr: \"%s\", loc: \"%s\"}%s"
          (Undefined.stringFromUndefined_behaviour ub)
          (String.escaped stderr)
          (Cerb_location.simple_location loc)
          (if is_charon then "\n" else "")
    | Error { msg; stderr } ->
        if is_charon then
          prerr_string stderr
        else if json then begin
          Yojson.to_buffer buf begin
            `Assoc [ "status", `String "Error"
                   ; "details", `Assoc [ "msg", `String msg
                                       ; "stderr", `String (String.escaped stderr) ] ]
          end
        end else begin
          begin if has_multiple then
            Buffer.add_string buf  ":\n"
          end;
          Buffer.add_string buf constrs_str;
          Printf.bprintf buf "Error {msg: \"%s\"}%s"
            msg
            (if is_charon then "\n" else "")
        end
  end;
  (if not is_charon then Buffer.add_string buf "\n" else ());
  flush_all ();
  Buffer.contents buf

(* TODO: make the output match the json format from charon2 (or at least add a option for that) *)
let batch_drive (file: 'a Core.file) args fs_state conf =
  Random.self_init ();
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run_aux.convert_file file in
  (* computing the value (or values if exhaustive) *)
  let initial_dr_st = Driver.initial_driver_state file fs_state in
  let values = Smt2.runND conf.exec_mode Impl_mem.cs_module (Driver.drive conf.concurrency file args) initial_dr_st in
  List.mapi (fun i (res, z3_strs, nd_st) ->
    let result = begin match res with
      | ND.Active dres ->
          let exit =
            match dres.Driver.dres_core_value with
              | Vloaded (LVspecified (OVinteger ival)) ->
                  Impl_mem.case_integer_value ival
                    (fun n  -> Specified n)
                    (fun () -> OtherValue dres.Driver.dres_core_value)
              | Vloaded (LVunspecified ty) ->
                  Unspecified ty
              | _ ->
                  OtherValue dres.Driver.dres_core_value in
          Defined { exit; stdout= dres.Driver.dres_stdout; stderr= dres.Driver.dres_stderr; blocked= dres.Driver.dres_blocked }
      | ND.Killed (dr_st, ND.Undef0 (loc, [])) ->
          let stderr = String.concat "" (Dlist.toList dr_st.Driver.core_state.Core_run.io.Core_run.stderr) in
          Error { msg= "[empty UB, probably a cerberus BUG]"; stderr }
      | ND.Killed (dr_st, ND.Undef0 (loc, ub::_)) ->
          let stderr = String.concat "" (Dlist.toList dr_st.Driver.core_state.Core_run.io.Core_run.stderr) in
          Undefined { ub; stderr; loc }
      | ND.Killed (dr_st, ND.Error0 (_, msg)) ->
          let stderr = String.concat "" (Dlist.toList dr_st.Driver.core_state.Core_run.io.Core_run.stderr) in
          Error { msg; stderr }
      | ND.Killed (dr_st, ND.Other dr_err) ->
          let stderr = String.concat "" (Dlist.toList dr_st.Driver.core_state.Core_run.io.Core_run.stderr) in
          Error { msg= string_of_driver_error dr_err; stderr }
    end in
    (z3_strs, result)
  ) values

let drive file args fs_state conf : execution_result =
  Random.self_init ();
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run_aux.convert_file file in
  (* computing the value (or values if exhaustive) *)
  let initial_dr_st = Driver.initial_driver_state file fs_state in
  let values = Smt2.runND conf.exec_mode Impl_mem.cs_module
      (Driver.drive conf.concurrency file args) initial_dr_st in
  let n_actives = List.length (List.filter isActive values) in
  let n_execs   = List.length values                        in
  Cerb_debug.print_debug 2 [] (fun () ->
    Printf.sprintf "Number of executions: %d actives (%d killed)\n" n_actives (n_execs - n_actives)
  );
  if n_actives = 0 && (n_execs - n_actives) = 0 then begin
    print_endline Cerb_colour.(ansi_format [Red]
      (Printf.sprintf "FOUND NO ACTIVE EXECUTION (with %d killed)\n" (n_execs - n_actives))
    );
    List.iteri (fun n exec ->
      match exec with
        | (ND.Active _, _, _) ->
            assert false
        | (ND.Killed (_, reason), z3_strs, st) ->
          (*
            let reason_str = match reason with
              | ND.Undef0 (loc, ubs) ->
                  "undefined behaviour[" ^ Cerb_location.location_to_string loc ^ "]: "
                  ^ Lem_show.stringFromList Undefined.stringFromUndefined_behaviour ubs
              | ND.Error0 (loc , str) ->
                  "static error[" ^ Cerb_location.location_to_string loc ^ "]: " ^ str
              | ND.Other str ->
                  string_of_driver_error str in
             *)
            begin
(*
      if reason_str = "reached unsatisfiable constraints" then
      print_endline Cerb_colour.(ansi_format [Red] 
        (Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_old_constraints st.ND.eqs) (String.concat "\n" (List.rev (Dlist.toList st.ND.log))))
      )
else
        Cerb_debug.print_debug 2 [] (fun () -> Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
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
            if Cerb_debug.get_debug_level () = 0 then
              (print_string dres.Driver.dres_stdout; prerr_string dres.Driver.dres_stderr; flush_all());
            
            Cerb_debug.print_debug 2 [] (fun () ->
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
              Cerb_debug.print_debug 2 [] (fun () -> Pp_cmm.dot_of_exeState conc_st str_v (Pp_cmm.pp_old_constraints st.ND.eqs)); *)
            
            ky := str_v_ :: !ky;
            ret := dres.Driver.dres_core_value :: !ret;
        ) else
          Cerb_debug.print_debug 4 [] (fun () ->
            "SKIPPING: " ^ if dres.Driver.dres_blocked then "(blocked)" else "" ^
            "eqs= " ^ "Pp_cmm.pp_old_constraints st.ND.eqs"
          );
        if conf.fs_dump then begin
          print_endline "File System:";
          print_endline @@ Sexplib.Sexp.to_string_hum @@ Sibylfs.sexp_of_fs_state st.Driver.fs_state
        end;
        if conf.trace then
          PPrint.ToChannel.pretty 1.0 80 stdout (Pp_trace.pp_trace @@ List.rev st.trace);

      | (ND.Killed (dr_st, ND.Undef0 (loc, ubs)), _, st) ->
          let stderr_xs = Dlist.toList dr_st.Driver.core_state.Core_run.io.Core_run.stderr in
          begin if List.length stderr_xs > 0 then
            let stderr_str = String.concat "" stderr_xs in
            Printf.fprintf stderr "BEGIN stderr\n%s\nEND stderr\n" stderr_str
          end;
          prerr_endline (Pp_errors.to_string (loc, Errors.(DRIVER (Driver_UB ubs))));
          if conf.trace then
            PPrint.ToChannel.pretty 1.0 80 stdout (Pp_trace.pp_trace @@ List.rev st.trace)

     (*
          let str_v = Cerb_location.location_to_string loc ^
            (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs)) in
          
          if not (List.mem str_v !ky) then (
            print_endline (
              Cerb_colour.(ansi_format [Red] ("UNDEFINED BEHAVIOUR[" ^ Cerb_location.location_to_string loc ^ "]:\n" ^
                (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs))
              ))
           );
            ky := str_v :: !ky;
          ) else
            ()
        *)
      
      | (ND.Killed (_, ND.Error0 (loc, str)), _, _) ->
          print_endline (Cerb_colour.(ansi_format [Red] ("IMPL-DEFINED STATIC ERROR[" ^ Cerb_location.location_to_string loc ^ "]: " ^ str)))
      
      | (ND.Killed (_, ND.Other reason), _, st) ->
          print_endline (Cerb_colour.(ansi_format [Red] ("OTHER ERROR: " ^ string_of_driver_error reason)))
  ) values;
  Exception.except_return !ret
