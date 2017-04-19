(* This script runs cerberus on the tests listed in the _tests file *)
let ($) f x = f x


(* BEGIN configuration section *)

let testsfile        = "_tests"
let cerberus_command = "csem --impl gcc_4.9.0_x86_64-apple-darwin10.8.0 --execute -r"

(* END configuration section *)


type test = {
  filename:        string;
  description:     string;
  expected_result: int;
}

let parse_testsfile () : test list =
  let ic = open_in testsfile in
  let ls = ref [] in
  begin
    try
      while true; do
        ls := input_line ic :: !ls
      done;
    with End_of_file ->
      close_in ic;
      ls := List.filter (fun str -> str <> "") $ List.rev !ls;
  end;
  snd $
    List.fold_left (fun ((kind, (n_opt, d_opt, r_opt)), acc) l ->
      if l.[0] = kind then
        match kind with
          | 'N' -> (('D', (Some (String.sub l 2 (String.length l - 2)), d_opt, r_opt)), acc)
          | 'D' -> (('R', (n_opt, Some (String.sub l 2 (String.length l - 2)), r_opt)), acc)
          | 'R' -> let Some n = n_opt in
                   let Some d = d_opt in
                   (('N', (None, None, None)), {
                      filename= n;
                      description= d;
                      expected_result= int_of_string $ String.sub l 2 (String.length l - 2)
                    } :: acc)
          | _   -> assert false
      else (
        prerr_endline $ "ERROR: while parsing `" ^ testsfile ^ "'";
        exit 2
      )
    ) (('N', (None, None, None)), []) !ls


let _ =
  let tests = List.rev $ parse_testsfile () in
  List.iter (fun test ->
    if not (Sys.file_exists test.filename) then (
      prerr_endline $ "ERROR: test file `" ^ test.filename ^ "' doesn't exists";
      exit 2;
    );
    
    let res = Sys.command $ cerberus_command ^ " " ^ test.filename ^ " > /dev/null" in
    if res <> test.expected_result then
      Printf.printf"[\x1b[31mFAILURE\x1b[0m] ==> %s, got: %d while expecting %d\n" test.filename res test.expected_result
    else
      Printf.printf"[\x1b[32mSUCCESS\x1b[0m] ==> %s\n" test.filename
  ) tests;
