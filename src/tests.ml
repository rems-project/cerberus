open Global
open Core
module E = Exception

(* use this to print a halting error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1

(* The return type of Core_run.run *)
type execution_result_full = 
(
  (
    (Core_run.taction_id Core.expr * ((Core_run.taction_id, Core_run.trace_action) Pmap.map * Core_run.E.trace)) Undefined.t *
    Core_run.E.state
  ) list list,
  Errors.t
) Exception.t

(* The type we use to compare results of executions *) 
type execution_result = (((Core_run.taction_id Core.expr) Undefined.t) Pset.set, Errors.t) Exception.t

(* TODO: proper printing for Undef and error *)
let pp_execution_result (result:execution_result) : string = 
  match result with
    | E.Result s ->
        "{" ^ (String.concat ", "
          (List.map (function
                       | Undefined.Defined x -> Boot.to_plain_string $ Pp_core.pp_expr x
                       | Undefined.Undef us  -> "Undef[" ^ (String.concat ", " $ List.map Undefined.string_of_undefined_behaviour us) ^ "]"
                       | Undefined.Error     -> "Error"
           ) (Pset.elements s))) ^ "}"
    | E.Exception e ->
        Errors.to_string e


let execution_result_equal (left:execution_result) (right:execution_result) : bool = 
  match left, right with 
  | E.Exception e1, E.Exception e2 -> e1 = e2
  | E.Result r1, E.Result r2       -> Pset.equal r1 r2
  | _                              -> false

let simplify_result (result : execution_result_full) : execution_result =
  match result with
    | E.Result [xs] ->
        E.Result (Pset.from_list Pervasives.compare (List.map (fun (u_x, st) -> Undefined.fmap fst u_x) xs))
    | E.Result [] ->
        (* TODO: find out why this happens, and restore the error: error "The execution returned no results." *)
        E.Result (Pset.empty Pervasives.compare) 
    | E.Result _ ->
        error "Multiple files were executed (we expected that only one file was executed)."
    | E.Exception s ->
        E.Exception s

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
    
let get_test_from_ints (file_name:string) (result:int list): test = 
  {file_name= file_name; 
   expected_result= E.Result (Pset.from_list Pervasives.compare (List.map (fun x -> Undefined.Defined (Econst (Cint (Num.num_of_int x)))) result)); }
  
let get_tests: test list = [get_test_from_ints "tests/concurrency/dummy.core" [11];
                            get_test_from_ints "tests/concurrency/MP+na_rel_acq_na.core" [1; 2];
                            get_test_from_ints "tests/concurrency/LB+acq_rel+acq_rel.core" [0; 1; 2];
                            get_test_from_ints "tests/concurrency/SB+rel_acq+rel_acq.core" [0; 1; 2; 3];
                            get_test_from_ints "tests/concurrency/dummy.c" [11];
                            get_test_from_ints "tests/concurrency/MP+na_rel_acq_na.c" [1; 2];
                            get_test_from_ints "tests/concurrency/LB+acq_rel+acq_rel.c" [0; 1; 2];
                            get_test_from_ints "tests/concurrency/SB+rel_acq+rel_acq.c" [0; 1; 2; 3]
                           ]
