open Global
open Core_run

(*
let rec string_of_thread_id = function
  | Cmm_aux_old.Tzero ->
      "0"
  | Cmm_aux_old.Tpar (n, tid) ->
      string_of_int n ^
      if Cmm_aux_old.tid_eq Cmm_aux_old.Tzero tid then "" else "." ^ string_of_thread_id tid
  | Cmm_aux_old.Tseq tid ->
      string_of_thread_id tid

let rec string_of_dyn_rule = function
  | Core_run_effect.Rule_Pos        -> "POS"
  | Core_run_effect.Rule_Neg        -> "NEG"
  | Core_run_effect.Rule_Pure_Hole  -> "PURE_HOLE"
  | Core_run_effect.Rule_Pure       -> "PURE"
  | Core_run_effect.Rule_If         -> "IF"
  | Core_run_effect.Rule_Let        -> "LET"
  | Core_run_effect.Rule_Ret        -> "RET"
  | Core_run_effect.Rule_Skip       -> "SKIP"
  | Core_run_effect.Rule_Proc       -> "== PROC =="
  | Core_run_effect.Rule_Wseq       -> "WSEQ"
  | Core_run_effect.Rule_Wseq_Neg   -> "WSEQ_NEG"
  | Core_run_effect.Rule_Sseq       -> "SSEQ"
  | Core_run_effect.Rule_Run        -> "RUN"
  | Core_run_effect.Rule_Save       -> "SAVE"
  | Core_run_effect.Rule_Unseq      -> "unseq"
  | Core_run_effect.Rule_ND         -> "nd"
  | Core_run_effect.Rule_Par        -> "par"
  | Core_run_effect.Rule_Output str -> "output: " ^ String.escaped str




let string_of_mem_value = function
  | Cmm_aux_old.Muninit     -> "uninit"
  | Cmm_aux_old.Mbase c     -> Boot_pprint.to_plain_string (Pp_core.pp_constant c)
  | Cmm_aux_old.Mobj addr   -> Boot_pprint.to_plain_string (Pp_core.pp_mem_addr addr) (* (_, x) -> Nat_big_num.to_string x *)
  | Cmm_aux_old.Mnull       -> "NULL"

let string_of_sym = function
  | Symbol.Symbol (_, Some str) -> str
  | Symbol.Symbol (n, None)     -> "a_" ^ string_of_int n

let string_of_trace_action tact =
  let f o =
    Boot_pprint.to_plain_string (Pp_core.pp_mem_addr o) in
(*
    "[" ^ (Boot_pprint.to_plain_string (PPrint.separate_map PPrint.dot (fun x -> PPrint.string (string_of_sym x)) (fst o))) ^
      ": @" ^ Nat_big_num.to_string (snd o) ^ "]" in
 *)
  match tact with
    | Core_run_effect.Tcreate (ty, o, tid) ->
        f o ^ " <= create {" ^ (Boot_pprint.to_plain_string (Pp_core.pp_ctype ty)) ^ "}" ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run_effect.Talloc (n, o, tid) ->
        f o ^ " <= alloc " ^ Nat_big_num.to_string n ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run_effect.Tkill (o, tid) ->
        "kill " ^ f o ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run_effect.Tstore (ty, o, n, mo, tid) ->
        "store {" ^ (Boot_pprint.to_plain_string (Pp_core.pp_ctype ty)) ^ 
          ", " ^ (Boot_pprint.to_plain_string (Pp_core.pp_memory_order mo)) ^ "} " ^ f o ^
          " " ^ string_of_mem_value n  ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run_effect.Tload (ty, o, v, mo, tid) ->
        "load {" ^ (Boot_pprint.to_plain_string (Pp_core.pp_ctype ty)) ^ 
          ", " ^ (Boot_pprint.to_plain_string (Pp_core.pp_memory_order mo)) ^ "} " ^
          f o ^ " = " ^ string_of_mem_value v ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run_effect.Trmw (ty ,o, e, d, mo, tid) ->
        "RMW {" ^ (Boot_pprint.to_plain_string (Pp_core.pp_ctype ty)) ^ 
          ", " ^ (Boot_pprint.to_plain_string (Pp_core.pp_memory_order mo)) ^ "} " ^
          f o ^ " = " ^ string_of_mem_value e ^
          " ==> " ^
          f o ^ " := " ^ string_of_mem_value d ^
        " thread: " ^ (string_of_thread_id tid)


let rec string_of_trace tact_map t =
(*
  let rec f = function
    | []      -> ""
    | [b]     -> string_of_trace_action (Pmap.find b tact_map)
    | b :: bs -> string_of_trace_action (Pmap.find b tact_map) ^ ", " ^ f bs
  in *) match t with
       | [] -> ""
       | (r, None) :: xs ->
           Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ "\n" ^
           string_of_trace tact_map xs
       | (r, Some (bs, a)) :: xs ->
           Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ " ==> " ^
           (* Colour.ansi_format [Colour.Green] (f $ Pset.elements bs)  ^ *)
           Colour.ansi_format [Colour.Red]  
           (Nat_big_num.to_string a) ^ ": " ^ string_of_trace_action (Pmap.find a tact_map) ^ "\n" ^ string_of_trace tact_map xs


(*
int, 'a) Exception.t -> (int, 'a) Exception.t

       but an expression was expected of type
(Core_run.taction_id Core.expr * ((Core_run.taction_id, Core_run.trace_action) Pmap.map * Core_run.E.trace)) list

*)

let pp_traces verbose i_execs =
  List.iter (fun (i, u_t) ->
    if verbose then (
      print_endline ("Trace #" ^ string_of_int i ^ ":");
      print_endline (match u_t with
        | (Undefined.Defined (v, (tact_map, t)), st) ->
            string_of_trace tact_map t ^ "\n\nValue: " ^ (Boot_pprint.to_plain_string (Pp_core.pp_expr v))
        | (Undefined.Undef ubs, st) ->
            "Undef[" ^ (String.concat ", " (List.map Undefined.string_of_undefined_behaviour ubs)) ^ "]"
        | (Undefined.Error, st) ->
            "Error"
    ));
    let (_, st) = u_t in
    print_string (Scanf.unescaped st.Core_run_effect.io.Core_run_effect.stdout)
    
  ) (numerote i_execs)


(*
    print_endline ("Trace #" ^ string_of_int i ^ ":\n" ^
    match u_t with
      | (Undefined.Defined0 (v, (tact_map, t)), st) ->
          string_of_trace tact_map t ^ "\n\nValue: " ^ (Boot_pprint.to_plain_string (Pp_core.pp_expr v))
      | (Undefined.Undef ubs, st) ->
          "Undef[" ^ (String.concat ", " (List.map Undefined.string_of_undefined_behaviour ubs)) ^ "]"
      | (Undefined.Error, st) ->
          "Error"
  )) (numerote i_execs);
  
  List.map (fun (i, u_t) ->
    print_endline ("Trace #" ^ string_of_int i ^ " = " ^
    match u_t with
      | (Undefined.Defined0 (v, (tact_map, t)), st) ->
          Boot_pprint.to_plain_string (Pp_core.pp_expr v)
      | (Undefined.Undef ubs, st) ->
          "Undef[" ^ (String.concat ", " (List.map Undefined.string_of_undefined_behaviour ubs)) ^ "]"
      | (Undefined.Error, st) ->
          "Error"
    )) (numerote i_execs)
 *)

(*
let pp_traces ts =
  List.map (fun (i, (v, (tact_map, t))) ->
    print_endline $ "Trace #" ^ string_of_int i ^ ":\n" ^
    string_of_trace tact_map t ^
    "\n\nValue: " ^ (Boot_pprint.to_plain_string $ Pp_core.pp_expr v)) $ numerote ts;
  List.map (fun (i, (v, _)) ->
    print_endline $ "Trace #" ^ string_of_int i ^ " = " ^
    (Boot_pprint.to_plain_string $ Pp_core.pp_expr v)) $ numerote ts
*)

*)


(* ======== RESET ======== *)

open Core_run_aux

let string_of_core_run_error = function
  | Illformed_program str ->
      "Illformed_program[" ^ str ^ "]"
  | Found_empty_stack str ->
      "Found_empty_stack[" ^ str ^ "]"
  | Reached_end_of_proc ->
      "Reached_end_of_proc"
  | Unknown_impl ->
      "Unknown_impl"
  | Unresolved_symbol sym ->
      "Unresolved_symbol[" ^ Pp_symbol.to_string_pretty sym ^ "]"
