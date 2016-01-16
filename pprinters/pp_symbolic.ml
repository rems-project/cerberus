open Symbolic
open Pp_prelude


let pp_symbolic_name = function
  | SYMBfsym sym -> !^ (Pp_symbol.to_string_pretty sym)
  | SYMBimpl iCst -> !^ (Implementation_.string_of_implementation_constant iCst)

let rec pp_symbolic ppA ppB = function
  | SYMBtrue ->
      !^ "true"
  | SYMBfalse ->
      !^ "false"
  | SYMBconst cst ->
      ppA cst
  | SYMBptrval ptr_val ->
      ppB ptr_val
  | SYMBmember_shift (symb, tag_sym, memb_ident) ->
      !^ "member_shift" ^^ P.parens (pp_symbolic ppA ppB symb ^^ P.comma ^^^ !^ (Pp_symbol.to_string_pretty tag_sym) ^^ P.comma ^^^ Pp_cabs.pp_cabs_identifier memb_ident)
  | SYMBctype ty ->
      Pp_core_ctype.pp_ctype ty
  | SYMBsym (_, sym) ->
      !^ (Pp_symbol.to_string_pretty sym)
  | SYMBnot symb ->
      !^ "not" ^^ P.parens (pp_symbolic ppA ppB symb)
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
      P.parens (!^ str_opt ^^^ pp_symbolic ppA ppB symb1 ^^^ pp_symbolic ppA ppB symb2)
  | SYMBite (symb1, symb2, symb3) ->
      P.parens (!^ "ite" ^^^ pp_symbolic ppA ppB symb1 ^^^ pp_symbolic ppA ppB symb2 ^^^ pp_symbolic ppA ppB symb3)
  | SYMBcall (symb_nm, symbs) ->
      P.parens (!^ "call" ^^^ pp_symbolic_name symb_nm ^^^ P.separate_map (P.space) (pp_symbolic ppA ppB) symbs)

