open Global_ocaml
open Core
module E = Exception

(* use this to print a halting error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1

(* The return type of Core_run.run *)
type execution_result_full = Exhaustive_driver.execution_result

(* The type we use to compare results of executions *) 
type execution_result = (string Pset.set, Errors.t8) Exception.t2

(* We forget the order of the results *)
let simplify_result (result : execution_result_full) : execution_result =
  match result with
  | Result l1   -> Result (Pset.from_list 
                           Pervasives.compare 
                           (List.map Boot_pprint.pp_core_expr l1)
                          )
  | Exception e -> Exception e
  
let pp_execution_result (result:execution_result) : string = 
  match result with
    | E.Result s ->
        "{" ^ (String.concat ", " (Pset.elements s)) ^ "}"
    | E.Exception e ->
        Pp_errors.to_string e

type test_result = (unit, string) Exception.t2

let compare_results (expected:execution_result) (actual_full:execution_result_full) : test_result =
  let actual: execution_result = simplify_result actual_full in
  if expected = actual then
    E.Result ()
  else
    E.Exception ("Expected: " ^ (pp_execution_result expected) ^ ". " ^
                 "Actual: " ^ (pp_execution_result actual) ^ ".")

type test = 
  { file_name: string;
    expected_result: execution_result;
  }
    
let get_test (file_name:string) 
             (def_results:int list) 
             (undef_results:Undefined.undefined_behaviour list): test = 
  let def_results2 = List.map 
                     (fun x -> Econst 
                                 (Naive_memory.MV_integer 
                                   (Symbolic.Symbolic_constant 
                                     (Big_int.big_int_of_int x)
                                   )
                                 )
                     ) 
                     def_results in
  let undef_results2 = List.map (fun x -> Eundef x) undef_results in
  let results_full = E.Result (def_results2 @ undef_results2) in
  let results_simplified = simplify_result results_full in
  {file_name= file_name; 
   expected_result= results_simplified; }
  
let get_tests: test list = 
  [(* Core programs *)
   get_test "tests/concurrency/coherence+rel_rel_acq.core" [1] [];
   get_test "tests/concurrency/coherence+init+rel_acq.core" [1] [];
   get_test "tests/concurrency/datarace+Rna+Rna.core" [0] [];
   get_test "tests/concurrency/datarace+Wna+Wna.core" [] [Undefined.Data_race];
   get_test "tests/concurrency/datarace+Rna+Wna.core" [] [Undefined.Data_race];
   get_test "tests/concurrency/datarace+Rna+Rna_Wna.core" [] [Undefined.Data_race];
   get_test "tests/concurrency/datarace+Wna_rel+acq_Rna.core" [0] [Undefined.Data_race];
   get_test "tests/concurrency/hb-mo-cycle+rel_rel_acq+rel_rel_acq.core" [0; 1; 2; 3] [];
   get_test "tests/concurrency/hb-mo-cycle+Wsc_Wsc_Rsc+Wsc_Wsc_Rsc.core" [1; 2; 3] [];
   get_test "tests/concurrency/MP+na_rel+acq_na.core" [1; 2] [];
   get_test "tests/concurrency/LB+acq_rel+acq_rel.core" [0; 1; 2] [];
   get_test "tests/concurrency/LB+Rsc_Wsc+Rsc_Wsc.core" [0; 1; 2] [];
   get_test "tests/concurrency/SB+rel_acq+rel_acq.core" [0; 1; 2; 3] [];
   get_test "tests/concurrency/SB+Wsc_Rsc+Wsc_Rsc.core" [1; 2; 3] [];
   get_test "tests/concurrency/WRC+rel+acq_rel+acq_acq.core" [1; 2] [];
   get_test "tests/concurrency/RMW-strong-equal.core" [5] [];
   get_test "tests/concurrency/RMW-strong-unequal.core" [0] [];
   get_test "tests/concurrency/RMW-weak-equal.core" [0; 5] [];
   get_test "tests/concurrency/RMW-weak-unequal.core" [0] [];
   get_test "tests/concurrency/IRIW+rel+rel+acq_acq+acq_acq.core" 
            [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] [];
   get_test "tests/concurrency/IRIW+Wsc+Wsc+Rsc_Rsc+Rsc_Rsc.core"
            [0; 1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] [];
   (* C programs *)
   get_test "tests/concurrency/MP+na_rel+acq_na.c" [1; 2] [];
   get_test "tests/concurrency/LB+acq_rel+acq_rel.c" [0; 1; 2] [];
   get_test "tests/concurrency/SB+rel_acq+rel_acq.c" [0; 1; 2; 3] []
   ]
