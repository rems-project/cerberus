open Symbolic
open Pp_prelude


let pp_symbolic_name = function
  | SYMBfsym sym -> !^ (Pp_symbol.to_string_pretty sym)
  | SYMBimpl iCst -> !^ (Implementation_.string_of_implementation_constant iCst)

let rec pp_symbolic = function
  | SYMBtrue ->
      !^ "true"
  | SYMBfalse ->
      !^ "false"
  | SYMBconst n ->
      !^ (Nat_big_num.to_string n)
  | SYMBctype ty ->
      Pp_core_ctype.pp_ctype ty
  | SYMBsym (_, sym) ->
      !^ (Pp_symbol.to_string_pretty sym)
  | SYMBop (op, symb1, symb2) ->
      let str_opt = match op with
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | Div -> "/"
        | Mod -> "mod"
        | Exp -> "exp"
        | Eq  -> "=="
        | Neq -> "/="
        | Lt  -> "<"
        | Ge  -> ">="
        | And -> "and"
        | Or  -> "or" in
      P.parens (!^ str_opt ^^^ pp_symbolic symb1 ^^^ pp_symbolic symb2)
  | SYMBite (symb1, symb2, symb3) ->
      P.parens (!^ "ite" ^^^ pp_symbolic symb1 ^^^ pp_symbolic symb2 ^^^ pp_symbolic symb3)
  | SYMBcall (symb_nm, symbs) ->
      P.parens (!^ "call" ^^^ pp_symbolic_name symb_nm ^^^ P.separate_map (P.space) pp_symbolic symbs)

