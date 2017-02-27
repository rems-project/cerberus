open Global_ocaml
open Core

open Pp_run

module ND  = Nondeterminism
module SEU = State_exception_undefined

let (>>=) = SEU.bind8

let isActive = function
  | (ND.Active _, _) ->
      true
  | _ ->
      false

type execution_result = (Core.pexpr list, Errors.error) Exception.exceptM



(* TODO: make the output match the json format from charon2 (or at least add a option for that) *)
let batch_drive (sym_supply: Symbol.sym UniqueId.supply) (file: unit Core.file) args cerb_conf : unit =
  Random.self_init ();
  
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run.convert_file file in
  
  (* computing the value (or values if exhaustive) *)
  let values = ND.runM0 (Driver.drive cerb_conf.concurrency cerb_conf.experimental_unseq sym_supply file args) in
  
  List.iter (function
    | ND.Active (stdout, (isBlocked, _, pe), _) ->
        let str_v = String_core.string_of_pexpr
            begin
              match pe with
              | Pexpr (ty, Core.PEval (Core.Vobject (Core.OVinteger ival))) ->
                      Pexpr (ty, Core.PEval ((match (Mem_aux.integerFromIntegerValue ival) with
                      | None -> Core.Vobject (Core.OVinteger ival) | Some n -> Core.Vobject (Core.OVinteger (Mem.integer_ival n))) ))
                  | _ ->
                      pe
              end in
        print_endline begin
          "Defined {value: \"" ^ str_v ^ "\", stdout: \"" ^ String.escaped stdout ^
          "\", blocked: \"" ^ if isBlocked then "true\"}" else "false\"}"
        end
    | ND.Killed (ND.Undef0 (_, ubs)) ->
        print_endline begin
          "Undefined {id: " ^ Lem_show.stringFromList Undefined.stringFromUndefined_behaviour ubs ^ "}"
        end
    | ND.Killed (ND.Error0 (_, str)) ->
        print_endline begin
          "Error {msg: " ^ str ^ "}"
        end
    | ND.Killed (ND.Other str) ->
        print_endline begin
          "Killed {msg: " ^ str ^ "}"
        end
  ) (List.map fst values);
  
  List.iter (fun (_, nd_st) ->
    print_endline ("CONSTRS ==> " ^ (Pp_constraints.pp_constraints nd_st.ND.eqs))
  ) values;
  
  List.iteri (fun i (_, nd_st) ->
    print_endline ("Log[" ^ string_of_int i ^ "]\n" ^ String.concat "\n" (Dlist.toList nd_st.ND.log) ^ "\nEnd[" ^ string_of_int i ^ "]" )
  ) values




let drive sym_supply file args cerb_conf : execution_result =
  Random.self_init ();
  
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run.convert_file file in
  
  (* computing the value (or values if exhaustive) *)
  let values = ND.runM0 (Driver.drive cerb_conf.concurrency cerb_conf.experimental_unseq sym_supply file args) in
  
  let n_actives = List.length (List.filter isActive values) in
  let n_execs   = List.length values                        in
  
  Debug_ocaml.print_debug 1 (Printf.sprintf "Number of executions: %d actives (%d killed)\n" n_actives (n_execs - n_actives));
  
  if n_actives = 0 then begin
    print_endline Colour.(ansi_format [Red]
      (Printf.sprintf "FOUND NO ACTIVE EXECUTION (with %d killed)\n" (n_execs - n_actives))
    );
    List.iteri (fun n (ND.Killed reason, st) ->
      let reason_str = match reason with
        | ND.Undef0 (loc, ubs) ->
            "undefined behaviour[" ^ Pp_errors.location_to_string loc ^ "]: " ^ Lem_show.stringFromList Undefined.stringFromUndefined_behaviour ubs
        | ND.Error0 (loc , str) ->
            "static error[" ^ Pp_errors.location_to_string loc ^ "]: " ^ str
        | ND.Other str ->
            str in
(*
      print_endline Colour.(ansi_format [Red] 
        (Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_constraints constraints) (String.concat "\n" (List.rev (Dlist.toList log))))
      )
*)
begin
      if reason_str = "reached unsatisfiable constraints" then
      print_endline Colour.(ansi_format [Red] 
        (Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_constraints st.ND.eqs) (String.concat "\n" (List.rev (Dlist.toList st.ND.log))))
      )
else
        Debug_ocaml.print_debug 2 (Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason_str (Pp_cmm.pp_constraints st.ND.eqs) (String.concat "\n" (List.rev (Dlist.toList st.ND.log))))

end
    ) values
  end;
  
  let ky  = ref [] in
  let ret = ref [] in
  
  List.iteri (fun n exec ->
    match exec with
      | (ND.Active (stdout, (is_blocked, conc_st, pe), (dr_steps, coreRun_steps)), st) ->
          let str_v = String_core.string_of_pexpr
              begin
                match pe with
                  | Pexpr (ty, Core.PEval (Core.Vobject (Core.OVinteger ival))) ->
                      Pexpr (ty, Core.PEval ((match (Mem_aux.integerFromIntegerValue ival) with
                      | None -> Core.Vobject (Core.OVinteger ival) | Some n -> Core.Vobject (Core.OVinteger (Mem.integer_ival n))) ))
                  | _ ->
                      pe
              end in
          let str_v_ = str_v ^ stdout in
          if true (* not (List.mem str_v_ !ky) *) then (
            if Debug_ocaml.get_debug_level () = 0 then
              (print_string stdout; flush_all());
            
            Debug_ocaml.print_debug 1 (
              Printf.sprintf "\n\n\n\n\nExecution #%d (value = %s) under constraints:\n=====\n%s\n=====\n" n str_v (Pp_cmm.pp_constraints st.ND.eqs) ^
              Printf.sprintf "BEGIN stdout\n%s\nEND stdout\n" stdout ^
              Printf.sprintf "driver steps: %d, core steps: %d\n" dr_steps coreRun_steps ^ 
              Printf.sprintf "BEGIN LOG\n%s\nEND LOG" (String.concat "\n" (List.rev (List.map (fun z -> "LOG ==> " ^ z) (Dlist.toList st.ND.log))))

(* ^
              Printf.sprintf "BEGIN LOG\n%s\nEND LOG\n" (String.concat "\n" (List.rev (Dlist.toList log))) *)
            );
          );
          if not (List.mem str_v_ !ky) && not is_blocked then (
            if cerb_conf.concurrency then
              Debug_ocaml.print_debug 2 (Pp_cmm.dot_of_exeState conc_st str_v (Pp_cmm.pp_constraints st.ND.eqs));
(*            print_string stdout; *)
            
            ky := str_v_ :: !ky;
            ret := pe :: !ret;
        ) else
          Debug_ocaml.print_debug 4 (
            "SKIPPING: " ^ if is_blocked then "(blocked)" else "" ^
            "eqs= " ^ Pp_cmm.pp_constraints st.ND.eqs
          );

      | (ND.Killed (ND.Undef0 (loc, ubs)), _) ->
          let str_v = Pp_errors.location_to_string loc ^
            (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs)) in
          
          if not (List.mem str_v !ky) then (
            print_endline (
              Colour.(ansi_format [Red] ("UNDEFINED BEHAVIOUR[" ^ Pp_errors.location_to_string loc ^ "]:\n" ^
                (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs))
              ))
           );
            ky := str_v :: !ky;
          ) else
            ()
      
      | (ND.Killed (ND.Error0 (loc, str)), _) ->
          print_endline (Colour.(ansi_format [Red] ("IMPL-DEFINED STATIC ERROR[" ^ Pp_errors.location_to_string loc ^ "]: " ^ str)))
      
      | (ND.Killed (ND.Other reason), st) ->
          Debug_ocaml.print_debug 5 (
            Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason (Pp_cmm.pp_constraints st.ND.eqs) (String.concat "\n" (List.rev (List.map (fun z -> "LOG ==> " ^ z) (Dlist.toList st.ND.log))))
          )
  ) values;
  Exception.return0 !ret



(*  
  Debug_ocaml.print_debug 1 (Printf.sprintf "Number of executions: %d\n" n_execs);
  
  let ky  = ref [] in
  let ret = ref [] in
  
  List.iteri (fun n exec ->
    match exec with
      | (ND.Active (stdout, (is_blocked, conc_st, pe), (dr_steps, coreRun_steps)), constraints) ->
          let str_v = String_core.string_of_pexpr
              begin
                match pe with
                  | Pexpr (ty, Core.PEval (Core.Vobject (Core.OVinteger ival))) ->
                      Pexpr (ty, Core.PEval ((match (Mem_aux.integerFromIntegerValue ival) with
                      | None -> Core.Vobject (Core.OVinteger ival) | Some n -> Core.Vobject (Core.OVinteger (Mem.integer_ival0 n))) ))
                  | _ ->
                      pe
              end in
          let str_v_ = str_v ^ stdout in
          if not (List.mem str_v_ !ky) then (
            if Debug_ocaml.get_debug_level () = 0 then
              (print_string stdout; flush_all());
            
            Debug_ocaml.print_debug 1 (
              Printf.sprintf "\n\n\n\n\nExecution #%d (value = %s) under constraints:\n=====\n%s\n=====\n" n str_v (Pp_cmm.pp_constraints constraints) ^
              Printf.sprintf "driver steps: %d, core steps: %d\n" dr_steps coreRun_steps
            );
          );
          if not (List.mem str_v_ !ky) && not is_blocked then (
            if cerb_conf.concurrency then
              Debug_ocaml.print_debug 2 (Pp_cmm.dot_of_exeState conc_st str_v (Pp_cmm.pp_constraints constraints));
(*            print_string stdout; *)
            
            ky := str_v_ :: !ky;
            ret := pe :: !ret;
        ) else
          Debug_ocaml.print_debug 4 (
            "SKIPPING: " ^ if is_blocked then "(blocked)" else "" ^
            "eqs= " ^ Pp_cmm.pp_constraints constraints
          );
      | (ND.Killed (ND.Other reason), constraints) ->
            Debug_ocaml.print_debug 1 (
              Printf.sprintf "\n\n\n\n\nExecution #%d (KILLED %s) under constraints:\n=====\n%s\n=====\n" n reason (Pp_cmm.pp_constraints constraints)
            );
  ) values;
  Exception.return2 !ret
*)
