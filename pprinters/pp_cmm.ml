open Cmm_csem


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

(*
let pp_constraints (Smt_wrapper.Assertions (_, xs)) =
  String.concat ";\n" xs
*)

open Constraints
let pp_constraints (Constraints xs) =
  let strs = List.map (fun z -> Pp_utils.to_plain_string (Pp_symbolic.pp_symbolic Pp_core.pp_value Pp_mem.pp_pointer_value z)) xs in
  "[" ^ String.concat ", " strs ^ "]"



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


let string_of_location ptr_val = Pp_utils.to_plain_string (Pp_mem.pp_pretty_pointer_value ptr_val)
let string_of_cvalue mval = Pp_utils.to_plain_string (Pp_mem.pp_pretty_mem_value mval)


let string_of_action_aux = function
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

let string_of_action act = String.escaped (string_of_action_aux act)


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


open Cmm_op

(*
let dot_of_exeState st value_str eqs_str =
  "digraph G {" ^
  "value [shape=box, label= \"Value: " ^ value_str ^ "\"];" ^
  "eqs [shape=box, label= \"" ^ eqs_str ^ "\"];" ^
  "subgraph cluster1 {" ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\";" ^ acc) st.symPre.sb "") ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\" [color=\"deeppink4\"];" ^ acc) st.symPre.asw "") ^

  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\" [color=\"red\"];" ^ acc) st.symWit.rf "") ^
  (Pset.fold (fun (act1, act2) acc -> "\"" ^ string_of_action act1 ^ "\" -> \"" ^
                                      string_of_action act2 ^ "\" [color=\"blue\"];" ^ acc) st.symWit.mo "") ^

  "}}"
*)





open Pp_prelude

let pp_action act =
  !^ (string_of_action act)

let pp_symState (st: Cmm_op.symState) : PPrint.document =
  let pp_aid act = P.dquotes (!^ ("aid_" ^ string_of_int (Cmm_csem.aid_of act))) in
  let (asw_colour, rf_colour, mo_colour) = ("deeppink4", "red", "blue") in
  
  let thread_docs = List.fold_left (fun acc act ->
    let tid = Cmm_csem.tid_of act in
    let xs' = (pp_aid act ^^^ P.brackets (!^ "label" ^^ P.equals ^^^ P.dquotes (pp_action act))) ::
      match Pmap.lookup tid acc with
        | Some xs ->
            xs
        | None ->
            [] in
    Pmap.add tid xs' acc
  ) (Pmap.empty compare) (Pset.elements st.symPre.actions) in
  
  !^ "digraph G" ^^^ P.braces (
    P.nest 2 (P.hardline ^^
      P.separate (P.semi ^^ P.hardline) begin
        (* listing the actions by their aid *)
        Pmap.fold (fun tid docs acc ->
          begin
            !^ ("subgraph cluster_" ^ string_of_int tid) ^^ P.braces (P.hardline ^^
              P.separate (P.semi ^^ P.hardline) begin
               (!^ "label" ^^ P.equals ^^^ P.dquotes (!^ ("Thread " ^ string_of_int tid))) :: docs
              end
            ^^ P.hardline)
          end :: acc
        ) thread_docs [] @


(*
        List.map (fun act ->
          pp_aid act ^^^ P.brackets (!^ "label" ^^ P.equals ^^^ P.dquotes (pp_action act))
        ) (Pset.elements st.symPre.actions) @
*)
        (* sb, asw, rf, mo *)
        List.map (fun (act1, act2) ->
        pp_aid act1 ^^^ P.minus ^^ P.rangle ^^^ pp_aid act2
      ) (Pset.elements st.symPre.sb) @
        List.map (fun (act1, act2) ->
        pp_aid act1 ^^^ P.minus ^^ P.rangle ^^^ pp_aid act2 ^^^ P.brackets (!^ "color" ^^ P.equals ^^^ P.dquotes (!^ asw_colour))
      ) (Pset.elements st.symPre.asw) @
        List.map (fun (act1, act2) ->
        pp_aid act1 ^^^ P.minus ^^ P.rangle ^^^ pp_aid act2 ^^^ P.brackets (!^ "color" ^^ P.equals ^^^ P.dquotes (!^ rf_colour))
      ) (Pset.elements st.symWit.rf) @
        List.map (fun (act1, act2) ->
        pp_aid act1 ^^^ P.minus ^^ P.rangle ^^^ pp_aid act2 ^^^ P.brackets (!^ "color" ^^ P.equals ^^^ P.dquotes (!^ mo_colour))
      ) (Pset.elements st.symWit.mo)
      end
    ) ^^ P.hardline
  )


let dot_of_exeState st _ _ =
  Pp_utils.to_plain_string (pp_symState st)




let pp_execState st =
  dot_of_exeState st "" ""

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
