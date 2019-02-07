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

let start_log cmd log_file () =
  let oc = open_out log_file in
  output_string oc (cmd ^ "\n");
  close_out oc

let is_success log_file () =
  let ic = open_in log_file in
  let rec f () =
    try
      let l = input_line ic in
      if String.length l < 2 then f ()
      else
        let suff = String.sub l (String.length l - 2) 2 in
        if suff = ":)" then true
        else f ()
    with
    | End_of_file -> false in
  let success = f () in
  close_in ic;
  success

let run_tests h opts filenames =
  let opts = if opts = "" then "" else opts ^ " " in
  iter_on_c_files
    (fun filename ->
      print_string filename;
      flush Pervasives.stdout;
      let log_file = filename ^ ".log" in
      let cmd = "DYLD_LIBRARY_PATH=`ocamlfind query z3` ../../cerberus " ^ opts ^ filename ^ " >> " ^ log_file ^ " 2>&1" in
      start_log cmd log_file ();
      let r = Unix.system cmd in
      match r with
      | WEXITED 0 ->
        if is_success log_file () then (print_string (" " ^ start_green ^ "OK" ^ reset_colour ^ "\n"); flush Pervasives.stdout)
        else (print_string (" " ^ start_red ^ "FAIL" ^ reset_colour ^ "\n"); flush Pervasives.stdout)
      | WEXITED _ -> print_string (" " ^ start_red ^ "!!!FAILED!!!" ^ reset_colour ^ "\n"); flush Pervasives.stdout
      | _ -> failwith "TODO run_typing_tests")
    filenames


let main () =
  run_tests () "--bmc --bmc_conc --bmc-mode=linux --bmc-cat=$CERB_PATH/bmc/linux.cat" (my_readdir2 "concurrency/linux");
  run_tests () "--bmc --bmc_conc --bmc-mode=c --bmc-cat=$CERB_PATH/bmc/c11.cat" (my_readdir2 "concurrency/litmus")
  (* TODO: do some magic for RC11 *)

let _ = main ()