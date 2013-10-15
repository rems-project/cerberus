open Global
open Core
module E = Exception

(* use this to print a halting error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1

(* The return type of Core_run.run *)
type execution_result_full = 
         ((Core_run.taction_id Core.expr *
           ((Core_run.taction_id, Core_run.trace_action) Pmap.map *
            (Core_run.dyn_rule * (Core_run.taction_id Debug.set * Core_run.taction_id) option) list)
          ) list list, 
          Errors.t)
         Exception.t

(* The type we use to compare results of executions *) 
type execution_result = ((Core_run.taction_id Core.expr) Pset.set, Errors.t) Exception.t

let pp_execution_result (result:execution_result) : string = 
  match result with
  | E.Result s    -> "{" ^ (String.concat ", " (List.map (fun x -> Boot.to_plain_string $ Pp_core.pp_expr x) (Pset.elements s))) ^ "}"
  | E.Exception e -> Errors.to_string e

let execution_result_equal (left:execution_result) (right:execution_result) : bool = 
  match left, right with 
  | E.Exception e1, E.Exception e2 -> e1 = e2
  | E.Result r1, E.Result r2       -> Pset.equal r1 r2
  | _                              -> false

let simplify_result (result : execution_result_full) : execution_result = 
  match result with
  | E.Result [list] -> E.Result (Pset.from_list Pervasives.compare (List.map (fun (x, _) -> x) list))
  | E.Result []     -> (* TODO: find out why this happens, and restore the error: error "The execution returned no results." *)
                       E.Result (Pset.empty Pervasives.compare) 
  | E.Result _      -> error "Multiple files were executed (we expected that only one file was executed)."
  | E.Exception s   -> E.Exception s
  
type test_result = (unit, string) Exception.t

let compare_results (expected:execution_result) (actual_full:execution_result_full) : test_result =
  let actual: execution_result = simplify_result actual_full in
  if execution_result_equal expected actual then
    E.Result ()
  else
    E.Exception ("Expected: " ^ (pp_execution_result expected) ^ ". Actual: " ^ (pp_execution_result actual) ^ ".")

type test = 
  { file_name: string;
    expected_result: execution_result;
  }
    
let get_test (file_name:string) (result:(Core_run.taction_id Core.expr) list): test = 
  {file_name= file_name; 
   expected_result= E.Result (Pset.from_list Pervasives.compare result); }
  
let get_tests: test list = [get_test "tests/concurrency/dummy.c" [Econst (Cint (Num.num_of_int 11))];
                            get_test "tests/concurrency/LB+acq_rel+acq_rel.c" []]
