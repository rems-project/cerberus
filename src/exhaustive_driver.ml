

(*
file zero ->
         Exception.t (list (U.t ((Core.expr E.taction_id) * (Map.map E.taction_id E.trace_action * E.trace)) * E.state)) Errors.t
*)

open Core


module SEU = State_exception_undefined

let (>>=) = SEU.bind4









(*
type thread_state0 = {
  arena0: action_id        expr;
  stack0: action_id        stack;
(*  current_proc: expr action_id;   (* TODO: what is that for? *) *)
}


(* TODO: more *)
(* File "_lem/core_run2.lem", line 438, character 1 to line 440, character 2 *)
type io_state0 = {
  stdout0: string;
}

(* File "_lem/core_run2.lem", line 442, character 1 to line 445, character 2 *)
type core_state0 = {
  thread_states: (thread_id * thread_state0) list;
  io0:            io_state0;
}
*)




let string_of_core_run_error = function
  | Core_run2_aux.Illformed_program str ->
      "Illformed_program[" ^ str ^ "]"
  | Core_run2_aux.Found_empty_stack ->
      "Found_empty_stack"
  | Core_run2_aux.Reached_end_of_proc ->
      "Reached_end_of_proc"
  | Core_run2_aux.Unknown_impl ->
      "Unknown_impl"
  | Core_run2_aux.Unresolved_symbol ->
      "Unresolved_symbol"



(*
let rec loop file dr_st =
  print_core_state dr_st.Driver.core_state;
  
  let dr_sts' = Driver.driver_step dr_st in
  List.iter (fun (_, a) -> loop file a) dr_sts'
*)
  
(*  
  let steps = Core_run2.core_steps file st in
  
  if List.length steps == 0 then
    failwith "empty list of steps"
  else begin
    print_endline "Possible steps:";
    
    List.iteri (fun i step ->
      print_endline (string_of_int i ^
        match step with
          | Core_run2.Step_action_request (str, tid, request) ->
              "- action request (" ^ str ^ ") with thread " ^ Big_int.string_of_big_int tid
          | Core_run2.Step_tau (str, tid, _) ->
              "- tau transition (" ^ str ^ ") with thread " ^ Big_int.string_of_big_int tid
          | Core_run2.Step_eval (str, tid, _) ->
              "- eval transition (" ^ str ^ ") with thread " ^ Big_int.string_of_big_int tid
          | Core_run2.Step_done pe ->
              "- done: " ^ Boot_pprint.pp_core_expr pe
      )
    ) steps;
    
    print_endline "Enter choice [number]:";
    let choice = read_int () in
    match List.nth steps choice with
      | Core_run2.Step_tau  (_, _, step)
      | Core_run2.Step_eval (_, _, step) ->
          (match step run_st with
            | Exception.Exception err ->
                failwith ("TODO: core_run error> " ^ string_of_core_run_error err)
            | Exception.Result (Undefined.Undef _, _) ->
                failwith "TODO: found an undefined behaviour"
            | Exception.Result (Undefined.Error, _) ->
                failwith "TODO: found a static-dynamic error"
            | Exception.Result (Undefined.Defined st', run_st') ->
                loop file st' run_st')
      | Core_run2.Step_done pe ->
          print_endline ("DONE, value: " ^ Boot_pprint.pp_core_expr pe)
  end
*)



open Pp_cmm



let pp_eqs eqs =
  let pp x = Boot_pprint.to_plain_string (Pp_core.pp_symbolic x) in
  List.fold_left (fun acc eq ->
    (match eq with
        | Symbolic.Symbolic_eq  (symb1, symb2) ->
            pp symb1 ^ " = " ^ pp symb2
        | Symbolic.Symbolic_neq (symb1, symb2) ->
            pp symb1 ^ " /= " ^ pp symb2
        | Symbolic.Symbolic_lt  (symb1, symb2) ->
            pp symb1 ^ " < " ^ pp symb2
        | Symbolic.Symbolic_ge  (symb1, symb2) ->
            pp symb1 ^ " >= " ^ pp symb2
   ) ^ ";\n" ^ acc
  ) "" eqs




let drive file =
  let main_body = 
    match Pmap.lookup file.main file.funs with
      | Some (retTy, [], expr_main) ->
          expr_main
      |  _ ->
          Pervasives.output_string stderr "ERROR: couldn't find the Core main function\n";
          exit (-1)
  in
  
  let file = Core_run2.convert_file file in
  
  
(*  let _ = loop file (Driver.initial_driver_state file) in *)
  
  let vs = Driver.driver (Driver.initial_driver_state file) in
(*  Printf.printf "Number of executions: %d\n" (List.length vs); *)
  
  List.iter (fun (n, (eqs, (preEx, v))) ->
(*
    Printf.printf "Execution #%d under constraints:\n" n;
    print_endline "=====";
    print_endline (pp_eqs eqs);
    print_endline "=====";
    Printf.printf "with pre_execution:\n%s\n" (Pp_cmm.dot_of_pre_execution preEx);
    Printf.printf "has value:\n  %s\n\n" (Boot_pprint.pp_core_expr v)
*)
    print_endline (Pp_cmm.dot_of_pre_execution preEx (Boot_pprint.pp_core_expr v) (pp_eqs eqs))
  ) (Global.numerote vs);
  
  Exception.return0 ()



