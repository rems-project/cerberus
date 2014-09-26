(* TODO: for now use Z3 via the command line ... *)

open Symbol
open Symbolic

open Z3


(*
let ctx : context ref =
  ref (assert false)


let mk_unit =
  








type assertions =
  Assertions of string list * string list

let is_empty_assertions =
  assert false

let empty_assertions =
  assert false

let combine_assertions =
  assert false

let is_unsat =
  assert false

let assert_eq =
  assert false
*)




(*
type assertion =
  | Assert_eq  of symbolic * symbolic
  | Assert_neq of symbolic * symbolic
  | Assert_lt  of symbolic * symbolic
  | Assert_ge  of symbolic * symbolic
*)


let string_of_operator = function
  | Add0 ->
      "+"
  | Sub0 ->
      "-"
  | Mul0 ->
      "*"
  | Div0 ->
      "/"
  | Mod0 ->
      "mod"
(*  | Exp *)


(* the list of string on the "left" are the declarations for symbols *)
let rec string_of_symbolic = function
  | SYMBconst n ->
      ([], Big_int.string_of_big_int n)
  | SYMBsym (_, Symbol (x, _)) ->
      let str = "sym_" ^ string_of_int x in
      ([str], str)
  | SYMBop (op, symb1, symb2) ->
      let (decls1, str1) = string_of_symbolic symb1 in
      let (decls2, str2) = string_of_symbolic symb2 in
      (decls1 @ decls2, "(" ^ string_of_operator op ^ " " ^ str1 ^ " " ^ str2 ^ ")")



type assertions =
  (* the first list are the symbol to declare, the second are things to asssert *)
  Assertions of string list * string list

let empty_assertions =
  Assertions ([], [])

let is_empty_assertions = function
  | Assertions (_, []) ->
      true
  | _ ->
      false


let unique_insert xs x =
  if List.mem x xs then xs else x :: xs



let combine_assertions (Assertions (decls1, xs1)) (Assertions (decls2, xs2)) =
  Assertions (List.fold_left unique_insert decls1 decls2, xs1 @ xs2)

let assert_ op_str symb1 symb2 (Assertions (decls, xs)) =
  let (decls1, str1) = string_of_symbolic symb1 in
  let (decls2, str2) = string_of_symbolic symb2 in
  Assertions (List.fold_left unique_insert decls (decls1 @ decls2), ("(" ^ op_str ^ " " ^ str1 ^ " " ^ str2 ^ ")") :: xs)


let assert_eq symb1 symb2 asserts =
  assert_ "=" symb1 symb2 asserts

let assert_neq symb1 symb2 (Assertions (decls, xs)) =
  let (decls1, str1) = string_of_symbolic symb1 in
  let (decls2, str2) = string_of_symbolic symb2 in
  Assertions (List.fold_left unique_insert decls (decls1 @ decls2), ("(not (= " ^ str1 ^ " " ^ str2 ^ "))") :: xs)

let assert_lt symb1 symb2 asserts =
  assert_ "<" symb1 symb2 asserts

let assert_ge symb1 symb2 asserts =
  assert_ ">=" symb1 symb2 asserts


let is_unsat (Assertions (decls, xs)) =
  if List.length xs = 0 then
    false
  else begin
(*    print_endline "calling Z3"; *)
    let (temp_name, temp_oc) = Filename.open_temp_file "" "" in
    output_string temp_oc (String.concat "\n" (List.map (fun x -> "(declare-fun " ^ x ^ " () Int)") decls));
    output_string temp_oc (String.concat "\n" (List.map (fun x -> "(assert " ^ x ^ ")") xs));
    output_string temp_oc "(check-sat)";
    close_out temp_oc;
    
    let ic = Unix.open_process_in ("z3 -smt2 " ^ temp_name) in
    let response = input_line ic in
(*    print_endline ("Z3 says " ^ response); *)
    let res = match response with
      | "unsat" -> true
      | _       -> false in
    close_in ic;
    res
  end
