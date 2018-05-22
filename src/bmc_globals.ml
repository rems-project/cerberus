let g_initial_tid = -1 (* Must be < 0 *)
let g_max_inline_depth = 3
let g_dot_file = "dot_graph"

let g_output_to_dot = false

let g_max_function_depth = 1
let g_max_loop_depth = 2

let g_sequentialise = true


let g_print_files = false
let g_print_initial_file = true

let g_bmc_debug = 2

let g_print_stats = false

let g_all_execs = false
let g_sc_unique = false

(* true if only integer type used is Int_ *)
(* TODO: don't do as Core-to-Core rewrite *
 * bmc_line *)
let g_all_types = true

let g_max_precision = 128 (* 2 * max_precision hack *)


let g_bv = true
