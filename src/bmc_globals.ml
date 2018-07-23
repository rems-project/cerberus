open Z3

(* Z3 context config *)
let g_z3_ctx_cfg = [ ("model", "true")  (* Generate model *)
                   ; ("proof", "false") (* Disable proof generation *)
                   ]
let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver              = Solver.mk_solver g_ctx g_z3_solver_logic_opt

let g_macro_finder = true

(* true => use bit vector representation *)
let g_bv = true
let g_bv_precision = 32

let g_max_run_depth = 3    (* Maximum function call/run depth per call/run *)
let g_sequentialise = true (* Sequentialise Core *)

let g_concurrent_mode = true

let g_bmc_debug = 10

let g_single_threaded = true
