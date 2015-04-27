open Language
open Cmm_aux
open Cmm_csem
open Opsem
                        
let memory_order_tostring (mo:memory_order) : string = 
match mo with 
  | Cmm_csem.NA      -> "NA"
  | Cmm_csem.Seq_cst -> "Seq_cst"
  | Cmm_csem.Relaxed -> "Relaxed"
  | Cmm_csem.Release -> "Release"
  | Cmm_csem.Acquire -> "Acquire"
  | Cmm_csem.Consume -> "Consume"
  | Cmm_csem.Acq_rel -> "Acq_rel"          

let rec int_exp_tostring (e:e) : string = 
  match e with
  | E_Int n          -> Printf.sprintf "%i" n
  | E_Var v          -> Printf.sprintf "%s" v
  | E_Plus (e1, e2)  -> Printf.sprintf "%s + %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | E_Minus (e1, e2) -> Printf.sprintf "%s - %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
                                            
let rec bool_exp_tostring (be:be) : string = 
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

let rec statement_tostring (stmt:statement) : string = 
  match stmt with
  | S_Skip                    -> Printf.sprintf "skip"
  | S_Assign (v, e)           -> Printf.sprintf "%s := %s" v (int_exp_tostring e)
  | S_Cond (be, stmt1, stmt2) -> Printf.sprintf "if %s then %s else %s" 
                                 (bool_exp_tostring be)
                                 (statement_tostring stmt1)
                                 (statement_tostring stmt2)
  | S_Seq l                   -> String.concat "; " (List.map (fun i -> statement_tostring i) l)
  | S_Par (stmt1, stmt2)      -> Printf.sprintf "Thread1: %s\nThread2: %s"
                                 (statement_tostring stmt1)
                                 (statement_tostring stmt2) 

let program_tostring (p:program) : string =
  statement_tostring p  
  
let action_tostring (a:action) : string = 
  match a with
  | Load (aid, tid, mo, loc, value) -> Printf.sprintf "Load %s %s %i (aid: %i, thread %i)"
                                       (memory_order_tostring mo) loc value aid tid
  | Store (aid, tid, mo, loc, value) -> Printf.sprintf "Store %s %s %i (aid: %i, thread %i)"
                                       (memory_order_tostring mo) loc value aid tid

let actions_tostring (s:state) : string =
  String.concat ", " (List.map (fun (_, i) -> action_tostring i) 
                               (Pmap.bindings_list s.actions0))

let memory_tostring (s:state) : string =
  String.concat ", " (List.map (fun (v, n) -> Printf.sprintf "%s -> %i" v n)
                               (Pmap.bindings_list s.mem))

let state_tostring (s:state) : string = 
  Printf.sprintf "Memory: %s\nTrace: %s" (memory_tostring s) (actions_tostring s)
