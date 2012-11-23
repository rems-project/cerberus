open Str
open Unix

exception Missed_type_error

let rec read_in i =
  try
    let s = input_line i in
      s ^ "\n" ^ read_in i
  with
    | End_of_file ->
        ""

let get_tests () = 
  split (regexp "^[ \t]*===========*[ \t]*\n") (read_in Pervasives.stdin)

let do_test o test =
  let o' = open_out "test.lem" in
    output_string o' test;
    close_out o';
    let i = open_process_in "../../lem -hol -ocaml -lib ../../library test.lem" in
    let msg = read_in i in
    let stat = close_process_in i in
      match stat with
        | WEXITED(0) ->
                close_out o;
                raise Missed_type_error
        | WEXITED(_) ->
            output_string o test;
            output_string o "--------------------------------------------------------------------------------\n";
            output_string o msg;
            output_string o "================================================================================\n"
        | _ -> assert false

let _ =
  let tests = get_tests () in
  let o = open_out "results" in
    List.iter (do_test o) tests;
    close_out o

