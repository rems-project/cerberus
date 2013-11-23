open Global
open Core_run

let rec string_of_thread_id = function
  | Tzero         -> "0"
  | Tpar (n, tid) -> string_of_int n ^
                     if thread_id_eq Tzero tid then "" else "." ^ string_of_thread_id tid
  | Tseq tid      -> string_of_thread_id tid

let rec string_of_dyn_rule = function
  | Core_run.Rule_Pos       -> "POS"
  | Core_run.Rule_Neg       -> "NEG"
  | Core_run.Rule_Pure_Hole -> "PURE_HOLE"
  | Core_run.Rule_Pure      -> "PURE"
  | Core_run.Rule_If        -> "IF"
  | Core_run.Rule_Let       -> "LET"
  | Core_run.Rule_Ret       -> "RET"
  | Core_run.Rule_Skip      -> "SKIP"
  | Core_run.Rule_Proc      -> "== PROC =="
  | Core_run.Rule_Wseq      -> "WSEQ"
  | Core_run.Rule_Wseq_Neg  -> "WSEQ_NEG"
  | Core_run.Rule_Sseq      -> "SSEQ"
  | Core_run.Rule_Run       -> "RUN"
  | Core_run.Rule_Save      -> "SAVE"
  | Core_run.Rule_Unseq     -> "unseq"
  | Core_run.Rule_ND        -> "nd"
  | Core_run.Rule_Par       -> "par"



let string_of_mem_value = function
  | Core_run.Muninit     -> "uninit"
  | Core_run.Mbase c     -> Boot.to_plain_string $ Pp_core.pp_constant c
  | Core_run.Mobj (_, x) -> string_of_int x
  | Core_run.Mnull       -> "NULL"

let string_of_sym = function
  | (_, Some str) -> str
  | (n, None)     -> "a_" ^ string_of_int n

let string_of_trace_action tact =
  let f o =
    "[" ^ (Boot.to_plain_string $ PPrint.separate_map PPrint.dot (fun x -> PPrint.string (string_of_sym x)) (fst o)) ^
      ": @" ^ string_of_int (snd o) ^ "]" in
  match tact with
    | Core_run.Tcreate (ty, o, tid) ->
        f o ^ " <= create {" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ "}" ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run.Talloc (n, o, tid) ->
        f o ^ " <= alloc " ^ Num.string_of_num n ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run.Tkill (o, tid) ->
        "kill " ^ f o ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run.Tstore (ty, o, n, mo, tid) ->
        "store {" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ 
          ", " ^ (Boot.to_plain_string $ Pp_core.pp_memory_order mo) ^ "} " ^ f o ^
          " " ^ string_of_mem_value n  ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run.Tload (ty, o, v, mo, tid) ->
        "load {" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ 
          ", " ^ (Boot.to_plain_string $ Pp_core.pp_memory_order mo) ^ "} " ^
          f o ^ " = " ^ string_of_mem_value v ^
        " thread: " ^ (string_of_thread_id tid)
    | Core_run.Trmw (ty ,o, e, d, mo, tid) ->
        "RMW {" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ 
          ", " ^ (Boot.to_plain_string $ Pp_core.pp_memory_order mo) ^ "} " ^
          f o ^ " = " ^ string_of_mem_value e ^
          " ==> " ^
          f o ^ " := " ^ string_of_mem_value d ^
        " thread: " ^ (string_of_thread_id tid)


let rec string_of_trace tact_map t =
  match t with
    | [] -> ""
    | (r, None) :: xs ->
        Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ "\n" ^
        string_of_trace tact_map xs
    | (r, Some (bs, a)) :: xs ->
        Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ " ==> " ^
        (* Colour.ansi_format [Colour.Green] (f $ Pset.elements bs)  ^ *)
        Colour.ansi_format [Colour.Red]
          (string_of_int a) ^ ": " ^ string_of_trace_action (Pmap.find a tact_map) ^ "\n" ^ string_of_trace tact_map xs


let pp_traces i_execs =
  List.map (fun (i, u_t) ->
    print_endline $ "Trace #" ^ string_of_int i ^ ":\n" ^
    match u_t with
      | (Undefined.Defined (v, (tact_map, t)), st) ->
          string_of_trace tact_map t ^ "\n\nValue: " ^ (Boot.to_plain_string $ Pp_core.pp_expr v)
      | (Undefined.Undef ubs, st) ->
          "Undef[" ^ (String.concat ", " $ List.map Undefined.string_of_undefined_behaviour ubs) ^ "]"
      | (Undefined.Error, st) ->
          "Error"
  ) $ numerote i_execs;
  
  List.map (fun (i, u_t) ->
    print_endline $ "Trace #" ^ string_of_int i ^ " = " ^
    match u_t with
      | (Undefined.Defined (v, (tact_map, t)), st) ->
          Boot.to_plain_string $ Pp_core.pp_expr v
      | (Undefined.Undef ubs, st) ->
          "Undef[" ^ (String.concat ", " $ List.map Undefined.string_of_undefined_behaviour ubs) ^ "]"
      | (Undefined.Error, st) ->
          "Error"
  ) $ numerote i_execs
