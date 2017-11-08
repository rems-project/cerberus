open Unix

let log_oc = open_out_gen [Open_append] 0 "LOG"

let cerbCmd =
  "cerberus --cpp='cc -E -nostdinc -undef -D__cerb__ -I $CERB_PATH/include/c/libc -I $CERB_PATH/include/c/posix -DCSMITH_MINIMAL -I ../runtime' --sequentialise --exec"

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
  let (ic, _, ic2) as chans = open_process_full ("gtimeout 30s " ^ cerbCmd ^ " " ^ filename) (environment ()) in
  let str = collect_output ic in
  match close_process_full chans with
      | WEXITED n ->
          if n = 124 then
            Timeout
          else
            Done (n, str)
      | _ ->
          Error ("(Cerberus) failed to execute the binary of '" ^ filename ^ "'")


let should_stop = ref false


let call_csmith filename =
  let _ = Sys.command ("./gen.sh " ^ filename) in
  ()

let rec generate_test filename =
  call_csmith filename;
  match run_cc filename with
    | Timeout ->
        generate_test filename
    | Error str ->
        Pervasives.(output_string stderr (str ^ "\n"));
        exit 1
    | Done (n, stdout) ->
        (n, stdout)


let generate_and_run_test n =
  let filename = "csmith_" ^ string_of_int n ^ ".c" in
  print_string (filename ^ " --> ");
  let (n_cc, stdout_cc) = generate_test filename in
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
          output_string log_oc ("KO " ^ filename ^ "\n");
         )
  end;
  flush_all ()

let rec loop body n =
  if !should_stop then (
    close_out log_oc;
    print_endline ("Terminating, next index will be: " ^ string_of_int (n+1))
   ) else (
    body n;
    loop body (n+1)
   )



let sigint_handler _ =
  should_stop := true

let () =
  Sys.(set_signal sigint (Signal_handle sigint_handler));
  
  let last_index =
    let csmithFiles =
      List.filter (fun f ->
        Filename.check_suffix f ".c" &&
        try
          String.sub f 0 7 = "csmith_"
        with
          | Invalid_argument _ ->
              false
      ) (Array.to_list (Sys.readdir ".")) in
    List.fold_left (fun acc f ->
      let str = Filename.remove_extension f in
      let n = int_of_string (String.sub str 7 (String.length str - 7)) in
      if n > acc then n else acc
    ) 0 csmithFiles
  in
  print_endline ("Resuming with index: " ^ string_of_int (last_index + 1));
  
 loop generate_and_run_test (last_index + 1)
