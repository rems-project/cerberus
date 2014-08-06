open Core

open Pp_cmm
open Pp_run

module ND  = Nondeterminism
module SEU = State_exception_undefined

let (>>=) = SEU.bind5


let drive file =
  let main_body = 
    match Pmap.lookup file.main file.funs with
      | Some (retTy, [], expr_main) ->
          expr_main
      |  _ ->
          Pervasives.output_string stderr "ERROR: couldn't find the Core main function\n";
          exit (-1) in
  
  let file = Core_run.convert_file file in
  
  let (Nondeterminism.ND vs) = Driver.driver_notweak (Driver.initial_driver_state file) in
  
  Global_ocaml.print_debug 1 (Printf.sprintf "Number of executions: %d\n" (List.length vs));
  
  let ky = ref [] in
  List.iteri (fun n exec ->
    match exec with
      | ND.Active (log, constraints, (is_blocked, preEx, value)) ->
          let str_v = Boot_pprint.pp_core_expr value in
          if not (List.mem str_v !ky) && not is_blocked then (
            Global_ocaml.print_debug 2 (
              Printf.sprintf "Execution #%d under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
                n (pp_constraints constraints) (String.concat "\n" (Dlist.toList log))
            );
            print_endline (Pp_cmm.dot_of_pre_execution preEx str_v (pp_constraints constraints))
          ) else
            Global_ocaml.print_debug 2 (
              "SKIPPING: " ^
              if is_blocked then "(blocked)" else "" ^
              "eqs= " ^ pp_constraints constraints
            );
          
          ky := str_v :: !ky
      
      | ND.Killed (ND.Undef0 ubs, _, _) ->
          print_endline (
            Colour.(ansi_format [Red] (Printf.sprintf "UNDEFINED BEHAVIOUR:\n%s\n"
              (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs))
            ))
          )
      
      | ND.Killed (ND.Error0, _, _) ->
          print_endline (Colour.(ansi_format [Red]"IMPL-DEFINED STATIC ERROR"))
      
      | ND.Killed (ND.Other reason, log, constraints) ->
          Global_ocaml.print_debug 3 (
            Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason (pp_constraints constraints) (String.concat "\n" (Dlist.toList log))
          )
  ) vs
