open Unix

let log_oc =
  if Sys.file_exists "LOG" then
    Sys.rename "LOG" "LOG.old";
  open_out_gen [Open_creat; Open_wronly; Open_append] 0o640 "LOG"

let should_stop = ref false

let do_force =
  if Array.length Sys.argv > 1 then
    Array.exists (fun z -> z = "--force" || z = "-f") (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
  else
    false

let terminate () =
  close_out log_oc;
  print_endline "Terminating";
  exit 0



let cerbCmd =
  "./cerb_wrapper.sh"
(*
  "cerberus --cpp='cc -E -nostdinc -undef -D__cerb__ -I $CERB_PATH/include/c/libc -I $CERB_PATH/include/c/posix -DCSMITH_MINIMAL -I ../runtime' --sequentialise --exec"
*)

let ccCmd =
  "clang -DCSMITH_MINIMAL -I ../runtime -w"


let collect_output ic =
  begin 
    let acc = ref [] in
    try
      while true do
        acc := input_line ic :: !acc;
      done;
      "" (* ... *)
    with
      | End_of_file ->
          String.concat "\n" (List.rev !acc)
  end

type status =
  | Done of int * string
  | Timeout
  | Error of string

let run_cc filename =
  if Sys.file_exists "a.out" then
    Sys.remove "a.out";
  
  let ret = Sys.command (ccCmd ^ " " ^ filename ^ " 2> /dev/null") in
  if ret <> 0 then (
    Error ("CC failed to build '" ^ filename ^ "'")
  ) else (
    let (ic, _, _) as chans = open_process_full "gtimeout 5s ./a.out" (environment ()) in
    let str = collect_output ic in
    match close_process_full chans with
      | WEXITED n ->
          if n = 124 then
            Timeout
          else
            Done (n, str)
      | _ ->
          Error ("(CC) failed to execute the binary of '" ^ filename ^ "'")
  )

let run_cerb filename =
  let (ic, _, ic2) as chans = open_process_full ("gtimeout 45s " ^ cerbCmd ^ " " ^ filename) (environment ()) in
  let str = collect_output ic in
  match close_process_full chans with
      | WEXITED n ->
          if n = 124 then
            Timeout
          else
            Done (n, str)
      | _ ->
          Error ("(Cerberus) failed to execute the binary of '" ^ filename ^ "'")

let should_rerun filename =
  if not (Sys.file_exists "LOG.old") then
    true
  else begin
    let log_ic = open_in "LOG.old" in
    let rec loop () =
      try
        let str = input_line log_ic in
        if String.sub str 3 (String.length str - 3) = filename then begin
          match String.sub str 0 2 with
            | "XX" | "TO" | "KO" ->
                true
            | _ ->
                output_string log_oc (str ^ "\n");
                false
        end else
          loop ()
      with
        | End_of_file ->
            true in
    let ret = loop () in
    close_in log_ic;
    ret
  end

let run_test filename =
  if !should_stop then
    terminate ();
  
  if not (do_force || should_rerun filename) then
    print_endline ("Skipping " ^ filename)
  else begin
    print_string (filename ^ " --> ");
    begin match run_cc filename with
      | Timeout ->
          print_endline "\x1b[33mXX\x1b[0m";
          output_string log_oc ("XX " ^ filename ^ "\n")
      | Error str ->
          Pervasives.(output_string stderr (str ^ "\n"));
          exit 1
      | Done (n_cc, stdout_cc) ->
          begin match run_cerb filename with
            | Timeout ->
                print_endline "\x1b[33mTO\x1b[0m";
                output_string log_oc ("TO " ^ filename ^ "\n")
            | Error str ->
                Pervasives.(output_string stderr (str ^ "\n"));
                exit 1
            | Done (n_cerb, stdout_cerb) ->
                if n_cc = n_cerb && stdout_cc = stdout_cerb then (
                  print_endline "\x1b[32mOK\x1b[0m";
                  output_string log_oc ("OK " ^ filename ^ "\n")
                 ) else (
                  print_endline "\x1b[31mKO\x1b[0m";
                  output_string log_oc ("KO " ^ filename ^ "\n")
                 )
          end
    end;
    flush_all ()
  end

let sigint_handler _ =
  should_stop := true

let () =
  Sys.(set_signal sigint (Signal_handle sigint_handler));
  
  let csmithFiles =
    List.sort compare begin
      List.filter (fun f ->
        Filename.check_suffix f ".c"
      ) (Array.to_list (Sys.readdir "."))
    end in
  
  List.iter run_test csmithFiles;
  terminate ()
