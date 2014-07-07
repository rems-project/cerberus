open Cmm_master

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
  "@" ^ Big_int.string_of_big_int n

let string_of_cvalue = function
  | Mem.MV_integer (Symbolic.Symbolic_constant n) ->
      Big_int.string_of_big_int n
  | Mem.MV_integer symb ->
      "SYMB(" ^ Boot_pprint.to_plain_string (Pp_core.pp_symbolic symb) ^ ")"


let string_of_action = function
  | Lock (aid, tid, loc, lock) ->
      Printf.sprintf "Lock[%s]" (Big_int.string_of_big_int aid)
  | Unlock (aid, tid, loc) ->
      Printf.sprintf "Unlock[%s]" (Big_int.string_of_big_int aid)
  | Load (aid, tid, mo, loc, v) ->
      Printf.sprintf "%s: R_{%s} %s = %s"
        (Big_int.string_of_big_int aid) 
        (string_of_memory_order mo)
        (string_of_location loc)
        (string_of_cvalue v)

  | Store (aid, tid, mo, loc, v) ->
      Printf.sprintf "%s: W_{%s} %s := %s"
        (Big_int.string_of_big_int aid) 
        (string_of_memory_order mo)
        (string_of_location loc)
        (string_of_cvalue v)

  | RMW (aid, tid, mo, loc, v1, v2) ->
      Printf.sprintf "RMW[%s]" (Big_int.string_of_big_int aid)
  | Fence (aid, tid, mo) ->
      Printf.sprintf "Fence[%s]" (Big_int.string_of_big_int aid)
  | Blocked_rmw (aid, tid, loc) ->
      Printf.sprintf "Blocked_rmw[%s]" (Big_int.string_of_big_int aid)
  | Alloc (aid, tid, loc) ->
      Printf.sprintf "%s: Create %s"
        (Big_int.string_of_big_int aid) 
        (string_of_location loc)

  | Dealloc (aid, tid, loc) ->
      Printf.sprintf "Dealloc[%s]" (Big_int.string_of_big_int aid)


let string_of_pre_execution preEx =
  let str =
     Printf.sprintf "actions= {%s};\n" (Pset.fold (fun act acc -> string_of_action act ^ ", " ^ acc) preEx.actions "") ^
     Printf.sprintf "sb=      %s;\n" (Pset.fold (fun (act1, act2) acc -> "(" ^ string_of_action act1 ^ ", " ^
                                                                               string_of_action act2 ^ " ), " ^ acc) preEx.sb "") ^
     Printf.sprintf "asw=     %s;" (Pset.fold (fun (act1, act2) acc -> "(" ^ string_of_action act1 ^ ", " ^
                                                                               string_of_action act2 ^ " ), " ^ acc) preEx.asw "") in
  Printf.sprintf "preEx {\n%s\n}" str


let dot_of_pre_execution preEx =
  "digraph G {" ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\";" ^ acc) preEx.sb "") ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\" [color=\"deeppink4\"];" ^ acc) preEx.asw "") ^
  "}"



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
