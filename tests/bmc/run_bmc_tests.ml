#!/usr/bin/env ocaml unix.cma
(* run Cerberus Bounded Model-Checker tests *)

let start_red = "\027[31m"
let start_green = "\027[32m"
let reset_colour = "\027[0m"


let my_readdir dirname =
  let a = Sys.readdir dirname in
  Array.sort Pervasives.compare a;
  Array.to_list a

let my_readdir2 dirname =
  List.map (fun f -> dirname ^ "/" ^ f) (my_readdir dirname)


let iter_on_c_files f filenames =
  List.iter
    (fun filename ->
      if Filename.check_suffix filename ".c" then f filename
      else ())
    filenames

let write_to_file cmd log_file () =
  let oc = open_out log_file in
  output_string oc cmd;
  close_out oc

type skip_t =
  | Skip_nothing
  | Skip_all_linux
  | Skip_only_rcu

type config = {
  only_write_command : bool;
  skip : skip_t;
  produce_graphs : bool;
}

let run_test validator cfg model opts filename =
  print_string (model ^ " " ^ filename);
  let dir = (Filename.chop_suffix filename ".c") ^ "-" ^ model ^ "/" in
  let _ = Unix.system ("mkdir -p " ^ dir) in
  flush Pervasives.stdout;
  let cmd_file = dir ^ "cmd.sh" in
  let log_file = dir ^ "log.txt" in
  let cmd = "DYLD_LIBRARY_PATH=`ocamlfind query z3` ../../cerberus " ^ opts ^ filename ^ " > " ^ log_file ^ " 2>&1" in
  write_to_file cmd cmd_file ();
  if cfg.only_write_command then (print_string (" WRITTEN\n"); flush Pervasives.stdout)
  else
    let r = Unix.system cmd in
    match r with
    | WEXITED 0 ->
      if validator log_file () then
        (if cfg.produce_graphs then let _ = Unix.system ("mv graph_*.dot " ^ dir) in ();
         print_string (" " ^ start_green ^ "OK" ^ reset_colour ^ "\n"); flush Pervasives.stdout)
      else (print_string (" " ^ start_red ^ "FAIL" ^ reset_colour ^ "\n"); flush Pervasives.stdout);
    | WEXITED _ -> print_string (" " ^ start_red ^ "!!!ERROR!!!" ^ reset_colour ^ "\n"); flush Pervasives.stdout
    | _ -> failwith "TODO run_typing_tests"

let run_tests validator cfg model opts filenames =
  let opts = if opts = "" then "" else opts ^ " " in
  iter_on_c_files (fun filename -> run_test validator cfg model opts filename) filenames

let find_flags () =
  let flag_only_write_command = ref false in
  let flag_skip_rcu = ref false in
  let flag_skip_linux = ref false in
  let flag_no_graphs = ref false in
  let speclist = [
    ("--only-cmd", Arg.Set flag_only_write_command, "Only produces the command files");
    ("--skip-rcu", Arg.Set flag_skip_rcu, "Skip RCU tests");
    ("--skip-linux", Arg.Set flag_skip_linux, "Skip Linux tests");
    ("--no-graphs", Arg.Set flag_no_graphs, "Do not produce graphs")
  ] in
  let usage_msg = "run_bmc_tests:"
  in Arg.parse speclist print_endline usage_msg;
  let skip =
    if !flag_skip_rcu && !flag_skip_linux then (prerr_string "use at most one of --skip-rcu and --skip-linux"; exit 1)
    else if !flag_skip_rcu then Skip_only_rcu
    else if !flag_skip_linux then Skip_all_linux
    else Skip_nothing in
  { only_write_command = !flag_only_write_command; skip = skip; produce_graphs = not (!flag_no_graphs) }

let validator_of_line_validator line_validator log_file () =
  let ic = open_in log_file in
  let rec f () =
    try
      let l = input_line ic in
      if line_validator l then true else f ()
    with
    | End_of_file -> false in
  let success = f () in
  close_in ic;
  success

let smiley_line_validator l =
  let pattern = ":)" in
  if String.length l < String.length pattern then false
  else String.sub l (String.length l - 2) (String.length pattern) = pattern

let ub_line_validator l =
  let pattern = "UB found" in
  if String.length l < String.length pattern then false
  else String.sub l 0 (String.length pattern) = pattern

let smiley_validator log_file () = validator_of_line_validator smiley_line_validator log_file ()

let ub_validator log_file () = validator_of_line_validator ub_line_validator log_file ()

let main () =
  let cfg = find_flags () in
  let graph_opt = (if cfg.produce_graphs then " --bmc_output_model=true" else "") in
  (match cfg.skip with
  | Skip_all_linux -> ()
  | Skip_nothing | Skip_only_rcu ->
    run_tests smiley_validator cfg "linux" ("-D__memory_model_linux__ --bmc --bmc_conc --bmc-mode=linux --bmc-cat=$CERB_PATH/bmc/linux_without_rcu.cat" ^ graph_opt) (my_readdir2 "concurrency/linux-no-rcu"));
  (match cfg.skip with
  | Skip_all_linux | Skip_only_rcu -> ()
  | Skip_nothing ->
    run_tests smiley_validator cfg "linux" ("-D__memory_model_linux__ --bmc --bmc_conc --bmc-mode=linux --bmc-cat=$CERB_PATH/bmc/linux.cat" ^ graph_opt) (my_readdir2 "concurrency/linux-rcu"));
  run_tests smiley_validator cfg "c11" ("-D__memory_model_c11__ --bmc --bmc_conc --bmc-mode=c --bmc-cat=$CERB_PATH/bmc/c11.cat" ^ graph_opt) (my_readdir2 "concurrency/litmus");
  run_tests ub_validator cfg "c11" ("-D__memory_model_c11__ --bmc --bmc_conc --bmc-mode=c --bmc-cat=$CERB_PATH/bmc/c11.cat" ^ graph_opt) (my_readdir2 "concurrency/litmus-ub");
  run_tests smiley_validator cfg "rc11" ("-D__memory_model_rc11__ --bmc --bmc_conc --bmc-mode=c --bmc-cat=$CERB_PATH/bmc/rc11.cat" ^ graph_opt) (my_readdir2 "concurrency/litmus");
  run_tests ub_validator cfg "rc11" ("-D__memory_model_rc11__ --bmc --bmc_conc --bmc-mode=c --bmc-cat=$CERB_PATH/bmc/rc11.cat" ^ graph_opt) (my_readdir2 "concurrency/litmus-ub")

let _ = main ()
