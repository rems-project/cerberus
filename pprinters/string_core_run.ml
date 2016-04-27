let string_of_core_state st =
  List.fold_left (fun acc (tid, (_, th_st)) ->
    acc ^ 
    Printf.sprintf "Thread %s:\n" (string_of_int tid) ^
    Printf.sprintf "  arena= %s\n" (String_core.string_of_expr th_st.Core_run.arena) ^
    Printf.sprintf "  stack= %s\n" (String_core.string_of_stack th_st.Core_run.stack) ^ " \n"
  ) "" st.Core_run.thread_states
