open Cmm_master


(*
let pp_constraints (Constraints.Constraints asserts) =
  let pp x = Boot_pprint.to_plain_string (Pp_core.pp_symbolic x) in
  List.fold_left (fun acc eq ->
    (match eq with
        | Constraints.Assert_eq  (symb1, symb2) ->
            pp symb1 ^ " = " ^ pp symb2
        | Constraints.Assert_neq (symb1, symb2) ->
            pp symb1 ^ " /= " ^ pp symb2
        | Constraints.Assert_lt  (symb1, symb2) ->
            pp symb1 ^ " < " ^ pp symb2
        | Constraints.Assert_ge  (symb1, symb2) ->
            pp symb1 ^ " >= " ^ pp symb2
   ) ^ ";\\n" ^ acc
  ) "" asserts
*)

let pp_constraints (Smt_wrapper.Assertions (_, xs)) =
  String.concat ";\n" xs




let string_of_memory_order = function
  | NA ->
      "na"
  | Seq_cst ->
      "sc"
  | Relaxed ->
      "rlx"
  | Release ->
      "rel"
  | Acquire ->
      "acq"
  | Consume ->
      "cons"
  | Acq_rel ->
      "acq_rel"


module Mem = Naive_memory

let string_of_location (Mem.Pointer_nonnull n) =
  "@" ^ string_of_int n

let string_of_cvalue = function
  | Mem.MV_integer (Symbolic.SYMBconst n) ->
      Big_int.string_of_big_int n
  | Mem.MV_integer symb ->
      "SYMB(" ^ Boot_pprint.to_plain_string (Pp_core.pp_symbolic symb) ^ ")"


let string_of_action = function
  | Lock (aid, tid, loc, lock) ->
      Printf.sprintf "Lock[%d]" aid
  | Unlock (aid, tid, loc) ->
      Printf.sprintf "Unlock[%d]" aid
  | Load (aid, tid, mo, loc, v) ->
      Printf.sprintf "%d: R_{%s} %s = %s"
        aid 
        (string_of_memory_order mo)
        (string_of_location loc)
        (string_of_cvalue v)

  | Store (aid, tid, mo, loc, v) ->
      Printf.sprintf "%d: W_{%s} %s := %s"
        aid 
        (string_of_memory_order mo)
        (string_of_location loc)
        (string_of_cvalue v)

  | RMW (aid, tid, mo, loc, v1, v2) ->
      Printf.sprintf "RMW[%d]" aid
  | Fence (aid, tid, mo) ->
      Printf.sprintf "Fence[%d]" aid
  | Blocked_rmw (aid, tid, loc) ->
      Printf.sprintf "Blocked_rmw[%d]" aid
  | Alloc (aid, tid, loc) ->
      Printf.sprintf "%d: Create %s"
        aid 
        (string_of_location loc)

  | Dealloc (aid, tid, loc) ->
      Printf.sprintf "Dealloc[%d]" aid


let string_of_pre_execution preEx =
  let str =
     Printf.sprintf "actions= {%s};\n" (Pset.fold (fun act acc -> string_of_action act ^ ", " ^ acc) preEx.actions "") ^
     Printf.sprintf "sb=      %s;\n" (Pset.fold (fun (act1, act2) acc -> "(" ^ string_of_action act1 ^ ", " ^
                                                                               string_of_action act2 ^ " ), " ^ acc) preEx.sb "") ^
     Printf.sprintf "asw=     %s;" (Pset.fold (fun (act1, act2) acc -> "(" ^ string_of_action act1 ^ ", " ^
                                                                               string_of_action act2 ^ " ), " ^ acc) preEx.asw "") in
  Printf.sprintf "preEx {\n%s\n}" str


let dot_of_pre_execution preEx value_str eqs_str =
  "digraph G {" ^
  "value [shape=box, label= \"Value: " ^ value_str ^ "\"];" ^
  "eqs [shape=box, label= \"" ^ eqs_str ^ "\"];" ^
  "subgraph cluster1 {" ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\";" ^ acc) preEx.sb "") ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\" [color=\"deeppink4\"];" ^ acc) preEx.asw "") ^
  "}}"



(*
  type pre_execution =
  <|  actions : set (action);
      threads : set (tid);
      lk      : location -> location_kind;
      sb      : set (action * action) ;
      asw     : set (action * action) ;
      dd      : set (action * action) ;
  |>
*)
