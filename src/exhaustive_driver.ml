open Global_ocaml
open Core

open Pp_cmm
open Pp_run

module ND  = Nondeterminism
module SEU = State_exception_undefined

let (>>=) = SEU.bind4


(*
let drive file args =
  let main_body = 
    match Pmap.lookup file.main file.funs with
      | Some (retTy, _, expr_main) ->
          expr_main
      |  _ ->
          Pervasives.output_string stderr "ERROR: couldn't find the Core main function\n";
          exit (-1) in
  
  let file = Core_run.convert_file file in
  let (Nondeterminism.ND vs) = Driver.drive (!!cerb_conf.concurrency) file args in
  
  Debug.print_debug 1 (Printf.sprintf "Number of executions: %d\n" (List.length vs));
  
  let isActive = function
    | ND.Active _ ->
        true
    | _ ->
        false in
  
  if List.length (List.filter isActive vs) = 0 then
    Debug.print_debug 0 "FOUND NO VALID EXECUTION";
  
  let ky = ref [] in
  let str_v = ref "" in
  List.iteri (fun n exec ->
    
    match exec with
      | ND.Active (log, constraints, (stdout, (is_blocked, preEx, value))) ->
          str_v := String_core.string_of_expr value;
          if not (List.mem str_v !ky) && not is_blocked then (
            Debug.print_debug 2 (
              Printf.sprintf "Execution #%d under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
                n (pp_constraints constraints) (String.concat "\n" (Dlist.toList log)) ^ "\n" ^
              (Pp_cmm.dot_of_pre_execution preEx !str_v (pp_constraints constraints))
            );
            print_string stdout;
          ) else
            Debug.print_debug 2 (
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
      
      | ND.Killed (ND.Error0 str, _, _) ->
          print_endline (Colour.(ansi_format [Red] ("IMPL-DEFINED STATIC ERROR: " ^ str)))
      
      | ND.Killed (ND.Other reason, log, constraints) ->
          Debug.print_debug 3 (
            Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason (pp_constraints constraints) (String.concat "\n" (Dlist.toList log))
          )
  ) vs;
  !str_v
*)

let isActive = function
  | ND.Active _ ->
      true
  | _ ->
      false



type execution_result = (Core_run_aux.core_run_annotation Core.expr list, Errors.t9) Exception.t3

let drive sym_supply file args with_concurrency : execution_result =
  let main_body = 
    match Pmap.lookup file.main file.funs with
      | Some (retTy, _, expr_main) ->
          expr_main
      |  _ ->
          Pervasives.output_string stderr "ERROR: couldn't find the Core main function\n";
          exit (-1) in
  
  let file = Core_run.convert_file file in
  let (Nondeterminism.ND vs) = Driver.drive with_concurrency sym_supply file args in
  
  Debug.print_debug 1 (Printf.sprintf "Number of executions: %d\n" (List.length vs));
  
  if List.length (List.filter isActive vs) = 0 then
    Debug.print_debug 0 "FOUND NO VALID EXECUTION";
  
  let ky  = ref [] in
  let ret = ref [] in
  
  List.iteri (fun n exec ->
    match exec with
      | ND.Active (log, constraints, (stdout, (is_blocked, preEx, value))) ->
          let str_v = String_core.string_of_expr value in
          if not (List.mem str_v !ky) && not is_blocked then (
            Debug.print_debug 2 (
              Printf.sprintf "Execution #%d under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
                n (pp_constraints constraints) (String.concat "\n" (Dlist.toList log)) ^ "\n"
            );
            if with_concurrency then
              print_endline (Pp_cmm.dot_of_pre_execution preEx str_v (pp_constraints constraints));
            print_string stdout;
            
            ky := str_v :: !ky;
            ret := value :: !ret;
        ) else
          Debug.print_debug 2 (
            "SKIPPING: " ^ if is_blocked then "(blocked)" else "" ^
            "eqs= " ^ pp_constraints constraints
          );





      | ND.Killed (ND.Undef0 ubs, _, _) ->
          print_endline (
            Colour.(ansi_format [Red] (Printf.sprintf "UNDEFINED BEHAVIOUR:\n%s\n"
              (String.concat "\n" (List.map (fun ub -> Undefined.pretty_string_of_undefined_behaviour ub) ubs))
            ))
          )
      
      | ND.Killed (ND.Error0 str, _, _) ->
          print_endline (Colour.(ansi_format [Red] ("IMPL-DEFINED STATIC ERROR: " ^ str)))
      
      | ND.Killed (ND.Other reason, log, constraints) ->
          Debug.print_debug 3 (
            Printf.sprintf "Execution #%d (KILLED: %s) under constraints:\n=====\n%s\n=====\nBEGIN LOG\n%s\nEND LOG"
              n reason (pp_constraints constraints) (String.concat "\n" (Dlist.toList log))
          )
  ) vs;
  Exception.return0 !ret
