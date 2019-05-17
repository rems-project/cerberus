open Z3


(* TODO: move to bmc_conf *)

(* Z3 context config *)
let g_z3_ctx_cfg =
  let base_cfg = [ ("model", "true")  (* Generate model *)
                 ; ("proof", "false") (* Disable proof generation *)
                 ; ("auto_config", "true")
                 (*; ("model_compress", "false")*)
                 ] in
  (* For versions >= 4.8, we disable model_compress in order to
   * be able to easily query the model
   * (e.g. when generating graphs or returning the model to the user).
   *
   * This parameter did not exist before 4.8; setting model_compress to
   * false essentially reverts to the before-4.8 behaviour.
   *)
  if Z3.Version.major > 4 ||
     (Z3.Version.major = 4 && Z3.Version.minor >= 8) then
       ("model_compress", "false") :: base_cfg
  else base_cfg

let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver              = Solver.mk_solver g_ctx g_z3_solver_logic_opt

let g_macro_finder = true

let g_bv = false
(* Note: this might be used for implement << even in integer mode *)
let g_bv_precision = 33

let g_max_int_size = 32

(* ==== Experimental options ===== *)
(* TODO: get value from somewhere else *)
(*let g_ptr_size = 8*) (* Ocaml_implementation*)
let g_max_addr = 2147483648
let g_pnvi = true

(* If false, checks memory bindings at the same time as __BMC_ASSUMES *)
let g_incremental_smt = true

(* If true, prints raw location in Z3 (prov, addr) style.
 * Else, attempts to pretty print variable name. *)
let g_dbg_print_raw_loc = false

(* If true, displays Kill memory actions in the .do *)
let g_display_kills = false

type memory_mode =
  | MemoryMode_C
  | MemoryMode_Linux

(*let g_memory_mode = MemoryMode_C*)

type bmc_conf = {
  max_run_depth       : int;
  max_core_call_depth : int;
  sequentialise   : bool;
  concurrent_mode : bool;
  memory_mode     : memory_mode;
  model_file      : string;
  parse_from_model : bool;

  fn_to_check     : string;
  find_all_execs  : bool;

  debug_lvl       : int;
  output_model    : bool;
}

let (!!) z = !z()

let bmc_conf : (unit -> bmc_conf) ref =
  ref (fun () -> failwith "bmc_conf is undefined")

let set bmc_max_depth bmc_seq bmc_conc bmc_fn bmc_debug bmc_all_execs
        bmc_output_model model_file_opt memory_mode =
  let (model_file, parse_from_model) =
    match model_file_opt with
    | Some model_file -> (model_file, true)
    | None -> ("bmc/example.c", false)
  in
  let conf = {
    max_run_depth   = bmc_max_depth;
    max_core_call_depth = if bmc_max_depth > 10 then bmc_max_depth else 10;
    sequentialise   = bmc_seq;
    concurrent_mode = bmc_conc;
    memory_mode     = memory_mode;
    model_file      = model_file;
    parse_from_model= parse_from_model;
    fn_to_check     = bmc_fn;
    find_all_execs  = bmc_all_execs;
    debug_lvl       = bmc_debug;
    output_model    = bmc_output_model;
  } in
  bmc_conf := fun () -> conf

