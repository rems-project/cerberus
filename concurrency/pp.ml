open Cmm_aux
open Cmm_master

let memory_order_tostring (mo:memory_order) : string = 
match mo with 
  | Cmm_master.NA      -> "NA"
  | Cmm_master.Seq_cst -> "Seq_cst"
  | Cmm_master.Relaxed -> "Relaxed"
  | Cmm_master.Release -> "Release"
  | Cmm_master.Acquire -> "Acquire"
  | Cmm_master.Consume -> "Consume"
  | Cmm_master.Acq_rel -> "Acq_rel"
  
let lock_outcome_tostring (l:lock_outcome) : string =
  match l with
  | Locked  -> "Locked"
  | Blocked -> "Blocked"

let action_tostring (a:action) : string = 
  match a with
  | Load (aid, tid, mo, loc, value)         -> Printf.sprintf "Load %s %i %i (aid: %i, thread %i)"
                                               (memory_order_tostring mo) loc value aid tid
  | Store (aid, tid, mo, loc, value)        -> Printf.sprintf "Store %s %i %i (aid: %i, thread %i)"
                                               (memory_order_tostring mo) loc value aid tid
  | Lock (aid, tid, loc, outcome)           -> Printf.sprintf "Lock %i %s (aid: %i, thread %i)"
                                               loc (lock_outcome_tostring outcome) aid tid
  | Unlock (aid, tid, loc)                  -> Printf.sprintf "Unlock %i (aid: %i, thread %i)"
                                               loc aid tid
  | RMW (aid, tid, mo, loc, value1, value2) -> Printf.sprintf "RMW %s %i %i %i (aid: %i, thread %i)"
                                               (memory_order_tostring mo) loc value1 value2 aid tid
  | Blocked_rmw (aid, tid, loc)             -> Printf.sprintf "Blocked_rmw %i (aid: %i, thread %i)"
                                               loc aid tid
  | Fence (aid, tid, mo)                    -> Printf.sprintf "Fence %s (aid: %i, thread %i)"
                                               (memory_order_tostring mo) aid tid
  | Alloc (aid, tid, loc)                   -> Printf.sprintf "Alloc %i (aid: %i, thread %i)"
                                               loc aid tid
  | Dealloc (aid, tid, loc)                 -> Printf.sprintf "Dealloc %i (aid: %i, thread %i)"
                                               loc aid tid

(*

let rec int_exp_tostring (e:expression) : string = 
  match e with
  | E_Int n          -> Printf.sprintf "%i" n
  | E_Var v          -> Printf.sprintf "%s" v
  | E_Plus (e1, e2)  -> Printf.sprintf "%s + %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | E_Minus (e1, e2) -> Printf.sprintf "%s - %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
                                            
let rec bool_exp_tostring (be:booleanExpression) : string = 
  match be with
  | Be_True          -> Printf.sprintf "true" 
  | Be_False         -> Printf.sprintf "false" 
  | Be_Eq (e1, e2)   -> Printf.sprintf "%s = %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | Be_Geq (e1, e2)  -> Printf.sprintf "%s >= %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | Be_Not e1        -> Printf.sprintf "~%s" (bool_exp_tostring e1)
  | Be_And (e1, e2)  -> Printf.sprintf "%s && %s"
                        (bool_exp_tostring e1)
                        (bool_exp_tostring e2)
  | Be_Or (e1, e2)   -> Printf.sprintf "%s || %s"
                        (bool_exp_tostring e1)
                        (bool_exp_tostring e2)

let rec statement_tostring (stmt:command) : string = 
  match stmt with
  | C_Skip                    -> Printf.sprintf "skip"
  | C_Store (v, e, mo)        -> Printf.sprintf "%s := %s (%s)" 
                                                v 
                                                (int_exp_tostring e) 
                                                (memory_order_tostring mo)
  | C_Load (v, e, mo, stmt)   -> Printf.sprintf "%s := %s (%s); %s" 
                                                v 
                                                (int_exp_tostring e) 
                                                (memory_order_tostring mo)
                                                (statement_tostring stmt)
  | C_If (be, stmt1, stmt2)   -> Printf.sprintf "if %s then %s else %s" 
                                 (bool_exp_tostring be)
                                 (statement_tostring stmt1)
                                 (statement_tostring stmt2)
  | C_Seq (stmt1, stmt2)      -> Printf.sprintf "%s; %s"
                                 (statement_tostring stmt1)
                                 (statement_tostring stmt2) 
  | C_Par (stmt1, stmt2)      -> Printf.sprintf "Thread1: %s\nThread2: %s"
                                 (statement_tostring stmt1)
                                 (statement_tostring stmt2) 

let actions_tostring (s:state) : string =
  String.concat ", " (List.map (fun (_, i) -> action_tostring i) 
                               (Pmap.bindings_list s.actions0))

let memory_tostring (s:state) : string =
  String.concat ", " (List.map (fun (v, n) -> Printf.sprintf "%s -> %i" v n)
                               (Pmap.bindings_list s.mem))

let state_tostring (s:state) : string = 
  Printf.sprintf "Memory: %s\nTrace: %s" (memory_tostring s) (actions_tostring s)
*)
