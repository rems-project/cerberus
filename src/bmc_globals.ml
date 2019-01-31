open Z3


(* TODO: move to bmc_conf *)

(* Z3 context config *)
let g_z3_ctx_cfg = [ ("model", "true")  (* Generate model *)
                   ; ("proof", "false") (* Disable proof generation *)
                   ]
let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver              = Solver.mk_solver g_ctx g_z3_solver_logic_opt

let g_macro_finder = true

let g_bv = false
let g_bv_precision = 33

(* ==== Experimental options ===== *)
(* TODO: get value from somewhere else *)
let g_ptr_size = 8 (* Ocaml_implementation*)
let g_max_addr = 2147483648
let g_pnvi = true

(*let g_model_file = "bmc/example.cat"*)

type memory_mode =
  | MemoryMode_C
  | MemoryMode_Linux

let g_memory_mode = MemoryMode_C

type bmc_conf = {
  max_run_depth     : int;
  max_core_call_depth : int;
  sequentialise   : bool;
  concurrent_mode : bool;

  fn_to_check     : string;
  find_all_execs  : bool;

  debug_lvl       : int;
  output_model    : bool;
}

let (!!) z = !z()

let bmc_conf : (unit -> bmc_conf) ref =
  ref (fun () -> failwith "bmc_conf is undefined")

let set bmc_max_depth bmc_seq bmc_conc bmc_fn bmc_debug bmc_all_execs
        bmc_output_model =
  bmc_conf := fun () ->
  { max_run_depth   = bmc_max_depth;
    max_core_call_depth = if bmc_max_depth > 10 then bmc_max_depth else 10;
    sequentialise   = bmc_seq;
    concurrent_mode = bmc_conc;
    fn_to_check     = bmc_fn;
    find_all_execs  = bmc_all_execs;
    debug_lvl       = bmc_debug;
    output_model    = bmc_output_model;
  }
