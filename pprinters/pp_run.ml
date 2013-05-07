open Global
open Core_run

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
  | Core_run.Rule_Run       -> "RUN"
  | Core_run.Rule_Save      -> "SAVE"
  | Core_run.Rule_Unseq     -> "unseq"


let string_of_mem_value = function
  | Core_run.Muninit     -> "uninit"
  | Core_run.Mnum n      -> string_of_int n
  | Core_run.Mobj (_, x) -> string_of_int x


let string_of_trace_action = function
  | Core_run.Tcreate (ty, o) ->
      "@" ^ string_of_int (snd o) ^ " <= create {" ^ (Boot.to_plain_string $ Pp_ail.pp_ctype ty) ^ "}"
  | Core_run.Talloc (n, o) ->
      "@" ^ string_of_int (snd o) ^ " <= alloc " ^ string_of_int n
  | Core_run.Tkill o ->
      "kill @" ^ string_of_int (snd o)
  | Core_run.Tstore (ty, o, n) ->
      "store {" ^ (Boot.to_plain_string $ Pp_ail.pp_ctype ty) ^ "} @" ^ string_of_int (snd o) ^
      " " ^ string_of_mem_value n
  | Core_run.Tload (ty, o, v) ->
      "load {" ^ (Boot.to_plain_string $ Pp_ail.pp_ctype ty) ^ "} @" ^
      string_of_int (snd o) ^ " = " ^ string_of_mem_value v


let rec string_of_trace t =
  let rec f = function
    | []      -> ""
    | [b]     -> string_of_trace_action b
    | b :: bs -> string_of_trace_action b ^ ", " ^ f bs
  in match t with
       | [] -> ""
       | (r, None) :: xs ->
           Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ "\n" ^
           string_of_trace xs
       | (r, Some (bs, (_, a))) :: xs ->
           Colour.ansi_format [Colour.Blue] (string_of_dyn_rule r) ^ " ==> " ^
           (* Colour.ansi_format [Colour.Green] (f $ Pset.elements bs)  ^ *)
           string_of_trace_action a ^ "\n" ^ string_of_trace xs


let pp_traces ts =
  List.map (fun (i, (v, t)) ->
    print_endline $ "Trace #" ^ string_of_int i ^ ":\n" ^
    string_of_trace t ^
    "\n\nValue: " ^ (Boot.to_plain_string $ Pp_core.pp_expr v)) $ numerote ts;
  List.map (fun (i, (v, t)) ->
    print_endline $ "Trace #" ^ string_of_int i ^ " = " ^
    (Boot.to_plain_string $ Pp_core.pp_expr v)) $ numerote ts
