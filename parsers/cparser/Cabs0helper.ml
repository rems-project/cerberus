(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Cabs0

let loc_hashtbl = Hashtbl.create 12
let next_loc = ref Coq_xH
let new_loc () =
  let res = !next_loc in
  next_loc := coq_Psucc res;
  res

let cabslu = new_loc ()
let _ =
  Hashtbl.add loc_hashtbl cabslu {
    Lexing.pos_fname= "cabs loc unknown";
    Lexing.pos_lnum= -10;
    Lexing.pos_bol= -10;
    Lexing.pos_cnum= -10
  }

let currentLoc lb : cabsloc =
  let res = new_loc () in
  let p = Lexing.lexeme_start_p lb in
  Hashtbl.add loc_hashtbl res p; (* (p.Lexing.pos_fname, p.Lexing.pos_lnum); *)
  res

let extern_loc loc =
  Hashtbl.find loc_hashtbl loc

(*********** HELPER FUNCTIONS **********)

let rec isStatic = function
    [] -> false
  | (SpecStorage STATIC) :: _ -> true
  | _ :: rest -> isStatic rest

let rec isExtern = function
    [] -> false
  | (SpecStorage EXTERN) :: _ -> true
  | _ :: rest -> isExtern rest

let rec isInline = function
    [] -> false
  | SpecInline :: _ -> true
  | _ :: rest -> isInline rest

let rec isTypedef = function
    [] -> false
  | SpecStorage TYPEDEF :: _ -> true
  | _ :: rest -> isTypedef rest


let get_definitionloc (d : definition) : cabsloc =
  match d with
  | FUNDEF(_, _, _, l) -> l
  | DECDEF(_, l) -> l
  | PRAGMA(_, l) -> l

let get_statementloc (s : statement0) : cabsloc =
begin
  match s with
  | NOP(loc) -> loc
  | COMPUTATION(_,loc) -> loc
  | BLOCK(_,loc) -> loc
  | If0(_,_,_,loc) -> loc
  | WHILE(_,_,loc) -> loc
  | DOWHILE(_,_,loc) -> loc
  | FOR(_,_,_,_,loc) -> loc
  | BREAK(loc) -> loc
  | CONTINUE(loc) -> loc
  | RETURN(_,loc) -> loc
  | SWITCH(_,_,loc) -> loc
  | CASE(_,_,loc) -> loc
  | DEFAULT(_,loc) -> loc
  | LABEL(_,_,loc) -> loc
  | GOTO(_,loc) -> loc
  | DEFINITION d -> get_definitionloc d
end

let string_of_cabsloc l =
  let loc = extern_loc l in
  Printf.sprintf "%s:%d:%d" loc.Lexing.pos_fname loc.Lexing.pos_lnum loc.Lexing.pos_bol (* TODO: maybe wrong *)

let format_cabsloc pp l =
  let loc = extern_loc l in
  Format.fprintf pp "%s:%d:%d" loc.Lexing.pos_fname loc.Lexing.pos_lnum loc.Lexing.pos_bol (* TODO: maybe wrong *)
