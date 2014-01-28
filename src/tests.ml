open Global
open Core
module E = Exception

let ($) f x = f x
let (-|) f g x = f (g x)


(* TODO: temporary *)
(* compare x y returns 0 if x is equal to y, a negative integer if x is less than y, and a positive integer if x is greater than y. The *)
(*
let compare_core_expr e1 e2 =



type 'a expr =
  (* pure expressions *)
  | Enull
  | Etrue
  | Efalse
  | Econst of constant2
  | Ectype of ctype0
  | Eaddr of mem_addr
  | Esym of sym
  | Eimpl of Implementation_.implementation_constant
  | Etuple of ( 'a expr) list
  | Enot of 'a expr
  | Eop of binop * 'a expr * 'a expr
  | Ecall of name0 * ( 'a expr) list
  
  (* undefined behaviour and late static error / failed assert *)
  | Eundef of Undefined.undefined_behaviour
  | Eerror
  
  (* potentialy effectful *)
  | Eskip
  | Elet of sym * 'a expr * 'a expr
  | Eif of 'a expr * 'a expr * 'a expr
  | Eproc of 'a Pset.set * sym * ( 'a expr) list (* Exactely like Ecall except that the body is impure *) (* TODO: discuss whether this is proper *)
  | Esame of 'a expr * 'a expr
  | Eaction of 'a paction
  
  (* sequencing operators *)
  | Eunseq of ( 'a expr) list

  | Ewseq of ( sym option) list * 'a expr * 'a expr
  | Esseq of ( sym option) list * 'a expr * 'a expr
  | Easeq of  sym option * 'a action0 * 'a paction (* this ctor doesn't exist at runtine *)
  
  (* indeterminately-sequenced expressions and boundary *) 
  | Eindet of 'a expr (* TODO: add unique indices *) (* this ctor doesn't exist at runtine *)
  | Ebound of Big_int.big_int * 'a expr (* this ctor doesn't exist at runtine *)
  
  (* Continuation operators *)
  (* TODO: may have to add the possibility of storing a number instead of a ctype (for dynamically allocated objects) *)
  | Esave of ksym * (sym * ctype0) list * 'a expr
  | Erun of 'a Pset.set * ksym * (sym * 'a expr) list
    (* TODO: need more for VLAs *)
  
  | Eret of 'a expr
  
  (* Non deterministic choice (resulting from indet expressions) *)
  (* TODO: this only exists for the second stage of dynamics (after core_indet) *)
  | End of ( 'a expr) list
  
  (* Parallel composition *)
  | Epar of ( 'a expr) list
  
  | Eshift of sym * 'a expr


(* TODO: this is a temporary, because I don't want to add pattern matching in Core, and those functions need it *)
  | Eis_scalar of 'a expr
  | Eis_integer of 'a expr
  | Eis_signed of 'a expr
  | Eis_unsigned of 'a expr


(* END TODO: temporary *)
*)




(* use this to print a halting error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1

(* The return type of Core_run.run *)
type execution_result_full = 
(
  (
    (Core_run_effect.taction_id Core.expr * ((Core_run_effect.taction_id, Core_run_effect.trace_action) Pmap.map * Core_run.E.trace)) Undefined.t1 *
    Core_run_effect.state0
  ) list list,
  Errors.t3
) Exception.t4

(* The type we use to compare results of executions *) 
type execution_result = (((Core_run_effect.taction_id Core.expr) Undefined.t1) Pset.set, Errors.t3) Exception.t4

(* TODO: proper printing for Undef and error *)
let pp_execution_result (result:execution_result) : string = 
  match result with
    | E.Result s ->
        "{" ^ (String.concat ", "
          (List.map (function
            | Undefined.Defined0 x -> Boot_ocaml.to_plain_string $ Pp_core.pp_expr x
                       | Undefined.Undef us  -> "Undef[" ^ (String.concat ", " $ List.map Undefined.string_of_undefined_behaviour us) ^ "]"
                       | Undefined.Error     -> "Error"
           ) (Pset.elements s))) ^ "}"
    | E.Exception e ->
        Pp_errors.to_string e


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

type test_result = (unit, string) Exception.t4

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
    
let get_test (file_name:string) 
             (def_results:int list) 
             (undef_results:(Undefined.undefined_behaviour list) list): test = 
  let def_results2 = List.map (fun x -> Undefined.Defined0 (Econst (Cint0 (Big_int.big_int_of_int x)))) def_results in
  let undef_results2 = List.map (fun x -> Undefined.Undef x) undef_results in
  let results = Pset.from_list Pervasives.compare (def_results2 @ undef_results2) in
  {file_name= file_name; 
   expected_result= E.Result results; }
  
let get_tests: test list = 
  [(* Core programs *)
   get_test "tests/concurrency/coherence+rel_rel_acq.core" [1] [];
   get_test "tests/concurrency/coherence+init+rel_acq.core" [1] [];
   get_test "tests/concurrency/datarace+Rna+Rna.core" [0] [];
   get_test "tests/concurrency/datarace+Wna+Wna.core" [] [[Undefined.Data_race]];
   get_test "tests/concurrency/datarace+Rna+Wna.core" [] [[Undefined.Data_race]];
   get_test "tests/concurrency/datarace+Rna+Rna_Wna.core" [] [[Undefined.Data_race]];
   get_test "tests/concurrency/datarace+Wna_rel+acq_Rna.core" [0] [[Undefined.Data_race]];
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
