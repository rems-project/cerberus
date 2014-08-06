let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str


let pp_ail_ctype ty = to_plain_string (Pp_ail.pp_ctype ty)
let pp_ail_expr e = to_plain_string (Pp_ail.pp_expression e)
let pp_core_expr e = to_plain_string (Pp_core.pp_expr e)
let pp_core_file f = to_plain_string (Pp_core.pp_file f)

let pp_core_params z = to_plain_string (Pp_core.pp_params z)
(* let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def) *)



open Core
let mk_string_of_continuation_element = function
  | Kunseq (es1, es2) ->
      fun z ->
        let str1 = List.fold_right (fun e acc -> pp_core_expr e ^ " || " ^ acc) es1 "" in
        let str2 = List.fold_right (fun e acc -> acc ^ "|| " ^ pp_core_expr e) es2 "" in
        "[ " ^ str1 ^ z ^ str2 ^ " ]"
  | Kwseq (_as, e) ->
      fun z ->
        let str = pp_core_expr e in
        "let weak TODO = " ^ z ^ " in " ^ str
  | Ksseq (_as, e) ->
      fun z ->
        let str = pp_core_expr e in
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




let pp_core_state st =
  List.fold_left (fun acc (tid, (_, th_st)) ->
    acc ^ 
    Printf.sprintf "Thread %s:\n" (string_of_int tid) ^
    Printf.sprintf "  arena= %s\n" (pp_core_expr th_st.Core_run.arena) ^
    Printf.sprintf "  stack= %s\n" (string_of_stack th_st.Core_run.stack) ^ " \n"
  ) "" st.Core_run.thread_states
