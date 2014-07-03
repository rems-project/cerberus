(*
file zero ->
         Exception.t (list (U.t ((Core.expr E.taction_id) * (Map.map E.taction_id E.trace_action * E.trace)) * E.state)) Errors.t
*)

open Core


module SEU = State_exception_undefined

let (>>=) = SEU.bind4


let mk_string_of_continuation_element = function
  | Kunseq (es1, es2) ->
      fun z ->
        let str1 = List.fold_right (fun e acc -> Boot_pprint.pp_core_expr e ^ " || " ^ acc) es1 "" in
        let str2 = List.fold_right (fun e acc -> acc ^ "|| " ^ Boot_pprint.pp_core_expr e) es2 "" in
        "[ " ^ str1 ^ z ^ str2 ^ " ]"
  | Kwseq (_as, e) ->
      fun z ->
        let str = Boot_pprint.pp_core_expr e in
        "let weak TODO = " ^ z ^ " in " ^ str
  | Ksseq (_as, e) ->
      fun z ->
        let str = Boot_pprint.pp_core_expr e in
        "let strong TODO = " ^ z ^ " in " ^ str

let string_of_continuation cont =
  List.fold_left (fun acc cont_elem -> mk_string_of_continuation_element cont_elem acc) "[]" cont


let rec string_of_stack = function
  | Stack_empty ->
      ""
  | Stack_cons (cont, Stack_empty) ->
      string_of_continuation cont
  | Stack_cons (cont, sk) ->
      string_of_continuation cont ^ " . " ^ string_of_stack sk




let print_core_state st =
  List.iter (fun (tid, (_, th_st)) ->
    Printf.printf "Thread %s:\n" (Big_int.string_of_big_int tid);
    Printf.printf "  arena= %s\n" (Boot_pprint.pp_core_expr th_st.Core_run2.arena0);
    Printf.printf "  stack= %s\n" (string_of_stack th_st.Core_run2.stack0);
    print_newline ()
  ) st.Core_run2.thread_states






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




let rec loop file st run_st =
  print_core_state st;
  
  
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
          | Core_run2.Step_thread_tau (str, tid, _) ->
              "- tau transition (" ^ str ^ ") with thread " ^ Big_int.string_of_big_int tid
          | Core_run2.Step_done pe ->
              "- done: " ^ Boot_pprint.pp_core_expr pe
      )
    ) steps;
    
    print_endline "Enter choice [number]:";
    let choice = read_int () in
    match List.nth steps choice with
      | Core_run2.Step_thread_tau (_, _, step) ->
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
  
  let _ =
    match Core_run2.init2 file Core_run2.initial_core_run_state with
      | Exception.Exception _ ->
          failwith "TODO: failed to init the core driver"
      | Exception.Result (Undefined.Defined st, run_st) ->
          loop file st run_st
  in
  
  Exception.return0 ()





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




(* File "_lem/core_run2.lem", line 450, character 1 to line 453, character 2 *)
type core_run_state = {
  tid_supply: thread_id    UniqueId.supply;
  symbol_supply: Symbol.t1 UniqueId.supply;
}







val Pmap.lookup: 'key -> ('key,'a) map -> 'a option


Core_run2.core_steps: Core.file action_id -> core_state -> ND.t core_step


type 'a fun_map = (sym, (core_type * (sym * core_base_type) list * 'a expr)) Pmap.map

type 'a file = {
  main   : sym;
  stdlib : 'a fun_map;
  impl   : 'a impl;
  defs   : (sym * core_base_type * 'a expr) list;
  funs   : 'a fun_map;
}


*)
