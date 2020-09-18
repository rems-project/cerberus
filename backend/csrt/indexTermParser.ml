(* open Pp *)
(* open TypeErrors *)
open Resultat
module StringMap = Map.Make(String)
module IT = IndexTerms


let rec parse_ast_to_t loc names (it: IT.parse_ast) = 
  let open IT in
  match it with
  | Num n -> 
     return (Num n)
  | Bool b -> 
     return (Bool b)
  | Add (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Add (it, it'))
  | Sub (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Sub (it, it'))
  | Mul (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Mul (it, it'))
  | Div (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Div (it, it'))
  | Exp (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Exp (it, it'))
  | Rem_t (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Rem_t (it, it'))
  | Rem_f (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Rem_f (it, it'))
  | Min (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Min (it, it'))
  | Max (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Max (it, it'))
  | EQ (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (EQ (it, it'))
  | NE (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (NE (it, it'))
  | LT (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (LT (it, it'))
  | GT (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (GT (it, it'))
  | LE (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (LE (it, it'))
  | GE (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (GE (it, it'))
  | Null it -> 
     let* it = parse_ast_to_t loc names it in
     return (Null it)
  | And its -> 
     let* its = ListM.mapM (parse_ast_to_t loc names) its in
     return (And its)
  | Or its -> 
     let* its = ListM.mapM (parse_ast_to_t loc names) its in
     return (Or its)
  | Impl (it, it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Impl (it, it'))
  | Not it -> 
     let* it = parse_ast_to_t loc names it in
     return (Not it)
  | ITE (it,it',it'') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     let* it'' = parse_ast_to_t loc names it'' in
     return (ITE (it,it',it''))
  | Tuple its ->
     let* its = ListM.mapM (parse_ast_to_t loc names) its in
     return (Tuple its)
  | Nth (bt, n, it') ->
     let* it' = parse_ast_to_t loc names it' in
     return (Nth (bt, n, it'))
  | Nil bt -> 
     return (Nil bt)
  | Cons (it,it') -> 
     let* it = parse_ast_to_t loc names it in
     let* it' = parse_ast_to_t loc names it' in
     return (Cons (it, it'))
  | List (its,bt) -> 
     let* its = ListM.mapM (parse_ast_to_t loc names) its in
     return (List (its, bt))
  | Head it ->
     let* it = parse_ast_to_t loc names it in
     return (Head it)
  | Tail it ->
     let* it = parse_ast_to_t loc names it in
     return (Tail it)
  | Member (tag, it, f) ->
     let* it = parse_ast_to_t loc names it in
     return (Member (tag, it, f))
  | MemberOffset (tag,t,f) ->
     let* it = parse_ast_to_t loc names it in
     return (MemberOffset (tag,it, f))
  | S string -> 
     begin match StringMap.find_opt string names with
     | Some sym -> return (S sym)
     | None -> fail loc (string ^ " unbound")
     end


(* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
let print_position lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error loc names lexbuf =
  let open Printf in
  try parse_ast_to_t loc names (Parser.prog Lexer.read lexbuf) with
    | Lexer.SyntaxError msg ->
       fail loc (sprintf "%s: %s" (print_position lexbuf) msg)
    | Parser.Error ->
       let tok = Lexing.lexeme lexbuf in
       fail loc (sprintf "%s: syntax error: %s" 
                   (print_position lexbuf) tok)
  

let parse loc names (* filename *) s =
  let lexbuf = Lexing.from_string s in
  (* lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename }; *)
  parse_with_error loc names lexbuf
