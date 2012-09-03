(* TODO:
 * 
 * Scoping:
 *   - Catch local hiding of globals for other targets
 *   - Identifier status in HOL
 *
 * Type definitions:
 *   - Mixed abbrevs and datatypes
 *   - type argument ordering
 *   - Semantically well-formed
 * 
 * Definitions:
 *   - Semantically well-formed
 *
 * Relation definitions:
 *   - Semantically well-formed
 *
 * Types:
 *   - Wildcards
 *
 * Expressions:
 *   - Let binding patterns
 *   - Fun binding patterns
 *   - Better operator substitution, esp. for precedence
 *
 * Patterns:
 *   - Record patterns
 *   - As patterns
 * Get rid of before_tyvars and after_tyvars
 *
 *)

open Typed_ast
open Output

let r = Ulib.Text.of_latin1

let gensym_tex_command =
  let n = ref 0 in
  function () ->
    n := 1 + !n;
    tex_command_escape (Ulib.Text.of_string (string_of_int !n))

let space = ws (Some [Ast.Ws (r" ")])

module type Target = sig
  val lex_skip : Ast.lex_skip -> Ulib.Text.t
  val need_space : Output.t' -> Output.t' -> bool

  val target : Ast.target option

  val path_sep : t
  val list_sep : t

  (* Types *)
  val typ_start : t
  val typ_end : t
  val typ_tup_sep : t
  val typ_sep : t
  val typ_fun_sep : t
  val typ_rec_start : t
  val typ_rec_end : t
  val typ_rec_sep : t
  val typ_constr_sep : t
  val typ_var : Ulib.Text.t

  (* Patterns *)
  val ctor_arg_start : t
  val ctor_arg_end : t
  val ctor_arg_sep : t
  val pat_as : t
  val pat_rec_start : t
  val pat_rec_end : t
  val pat_wildcard : t

  (* Constants *)
  val const_true : t
  val const_false : t
  val string_quote : Ulib.Text.t

  (* Expressions *)
  val case_start : t
  val case_sep1 : t
  val case_sep2 : t
  val case_line_sep : t
  val case_end : t
  val cond_if : t
  val cond_then : t
  val cond_else : t
  val field_access_start : t
  val field_access_end : t
  val fun_start : t
  val fun_end : t
  val fun_kwd : t
  val fun_sep : t
  val function_start : t
  val function_end : t
  val record_assign : t
  val recup_start : t
  val recup_middle : t
  val recup_end : t
  val recup_assign : t
  val val_start : t
  val let_start : t
  val let_in : t
  val let_end : t
  val begin_kwd : t
  val end_kwd : t
  val forall : t
  val exists : t
  val list_quant_binding : t
  val set_quant_binding : t
  val quant_binding_start : t
  val quant_binding_end : t
  val set_start :t
  val set_end :t
  val setcomp_binding_start : t
  val setcomp_binding_sep : t
  val setcomp_binding_middle : t
  val setcomp_sep : t
  val cons_op : t
  val set_sep : t
  val list_begin : t
  val list_end : t
  val first_case_sep : (Ast.lex_skips,t) Seplist.optsep

  (* Pattern and Expression tuples *)
  val tup_sep : t

  (* Value definitions *)
  val def_start : t
  val def_binding : t
  val def_end : t
  val def_sep : t
  val rec_def_header : lskips -> lskips -> Name.t -> t
  val rec_def_footer : Name.t -> t
  val letbind_sep : t
  val letbind_initial_sep : t
  val funcase_start : t
  val funcase_end : t
  val reln_start : t
  val reln_end : t
  val reln_sep : t
  val reln_clause_start : t
  val reln_clause_end : t

  (* Type defnitions *)
  val typedef_start : t
  val typedef_binding : t
  val typedef_end : t
  val typedef_sep : t
  val typedefrec_start : t
  val typedefrec_end : t
  val rec_start : t
  val rec_end : t
  val rec_sep : t
  val constr_sep : t
  val before_tyvars : t
  val after_tyvars : t
  val last_rec_sep : (Ast.lex_skips,t) Seplist.optsep
  val last_list_sep : (Ast.lex_skips,t) Seplist.optsep
  val last_set_sep : (Ast.lex_skips,t)Seplist.optsep 
  val first_variant_sep : (Ast.lex_skips,t) Seplist.optsep
  val type_params_pre : bool
  val type_abbrev_start : t
  val type_abbrev_sep : t
  val type_abbrev_end : t
  val type_abbrev_name_quoted : bool

  (* modules *)
  val module_module : t
  val module_struct : t
  val module_end : t
  val module_open : t



  (* TODO: remove some and none *)
  val some : Ident.t
  val none : Ident.t
end

module Identity : Target = struct
  open Str

  let lex_skip = function
    | Ast.Com(r) -> ml_comment_to_rope r
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  module S = Set.Make(String)

  let delim_regexp = regexp "^\\([][`;,(){}]\\|;;\\)$"

  let symbolic_regexp = regexp "^[-!$%&*+./:<=>?@^|~]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = 
    let f x =
      match x with
        | Kwd'(s) ->
            if is_delim s then
              (true,false)
            else if is_symbolic s then
              (false,true)
            else
              (false,false)
        | Ident'(r) ->
            (false, is_symbolic (Ulib.Text.to_string r))
        | Num' _ ->
            (false,false)
    in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2

  let target = None

  let path_sep = kwd "."
  let list_sep = kwd ";"

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "*"
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "->"
  let typ_rec_start = kwd "<|"
  let typ_rec_end = kwd "|>"
  let typ_rec_sep = kwd ";"
  let typ_constr_sep = kwd "of"
  let typ_var = r"'"
  
  let ctor_arg_start = emp
  let ctor_arg_end = emp
  let ctor_arg_sep = emp
  let pat_as = kwd "as"
  let pat_rec_start = kwd "<|"
  let pat_rec_end = kwd "|>"
  let pat_wildcard = kwd "_"

  let const_true = kwd "true"
  let const_false = kwd "false"
  let string_quote = r"\""

  let case_start = kwd "match"
  let case_sep1 = kwd "with"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "->"
  let case_end = kwd "end"
  let cond_if = kwd "if"
  let cond_then = kwd "then"
  let cond_else = kwd "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = kwd "fun"
  let fun_sep = kwd "->"
  let function_start = kwd "function"
  let function_end = kwd "end"
  let record_assign = kwd "="
  let recup_start = kwd "<|"
  let recup_middle = kwd "with"
  let recup_end = kwd "|>"
  let recup_assign = kwd "="
  let val_start = kwd "val"
  let let_start = kwd "let"
  let let_in = kwd "in"
  let let_end = emp
  let begin_kwd = kwd "begin"
  let end_kwd = kwd "end"
  let forall = kwd "forall"
  let exists = kwd "exists"
  let set_quant_binding = kwd "IN"
  let list_quant_binding = kwd "MEM"
  let quant_binding_start = kwd "("
  let quant_binding_end = kwd ")"
  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = kwd "forall"
  let setcomp_binding_sep = emp
  let setcomp_binding_middle = kwd "|"
  let setcomp_sep = kwd "|"
  let cons_op = kwd "::"
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let first_case_sep = Seplist.Optional

  let tup_sep = kwd ","

  let def_start = kwd "let"
  let def_binding = kwd "="
  let def_end = emp
  let def_sep = kwd "and"
  let rec_def_header sk1 sk2 _ = ws sk1 ^ kwd "let" ^ ws sk2 ^ kwd "rec"
  let rec_def_footer n = emp
  let letbind_sep = kwd "|" 
  let letbind_initial_sep = kwd "|"
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "indreln"
  let reln_end = emp
  let reln_sep = kwd "and"
  let reln_clause_start = kwd "forall"
  let reln_clause_end = emp

  let typedef_start = kwd "type"
  let typedef_binding = kwd "="
  let typedef_end = emp
  let typedef_sep = kwd "and"
  let typedefrec_start = kwd "type"
  let typedefrec_end = emp
  let rec_start = kwd "<|"
  let rec_end = kwd "|>"
  let rec_sep = kwd ";"
  let constr_sep = kwd "*"
  let before_tyvars = emp
  let after_tyvars = emp
  let type_abbrev_start = kwd "type"
  let last_rec_sep = Seplist.Optional
  let last_list_sep = Seplist.Optional
  let last_set_sep = Seplist.Optional
  let first_variant_sep = Seplist.Optional
  let type_params_pre = false
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp
  let type_abbrev_name_quoted = false
  let module_module = kwd "module"
  let module_struct = kwd "struct"
  let module_end = kwd "end"
  let module_open = kwd "open"

  let some = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"Some"))) Ast.Unknown
  let none = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"None"))) Ast.Unknown
end

module Html : Target = struct
  include Identity 
  let target = Some (Ast.Target_html None)

  let forall = kwd "&forall;"
  let exists = kwd "&exist;"
  let set_quant_binding = kwd "&isin;"
  let setcomp_binding_start = kwd "&forall;"
  let reln_clause_start = kwd "&forall;"

end

module Tex : Target = struct
  open Str

  let lex_skip = function _ -> r"DUMMY"

  module S = Set.Make(String)

  let delim_regexp = regexp "^\\([][`;,(){}]\\|;;\\)$"

  let symbolic_regexp = regexp "^[-!$%&*+./:<=>?@^|~]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = false

  let target = Some (Ast.Target_tex None)

  let tkwd s = kwd (String.concat "" ["\\lemkw{"; s;  "}"])
  let tkwdl s = kwd (String.concat "" ["\\lemkw{"; s;  "}"]) ^ texspace
  let tkwdr s = texspace ^ kwd (String.concat "" ["\\lemkw{"; s;  "}"]) 
  let tkwdm s = texspace ^ kwd (String.concat "" ["\\lemkw{"; s;  "}"]) ^ texspace

  let path_sep = kwd "." (* "`" *)
  let list_sep = kwd ";"

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "*"
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "\\rightarrow "
  let typ_rec_start = kwd "\\Mmagiclrec"
  let typ_rec_end = kwd "\\Mmagicrrec "
  let typ_rec_sep = kwd ";\\,"
  let typ_constr_sep = tkwdm "of"
  let typ_var = r"'"
  
  let ctor_arg_start = emp
  let ctor_arg_end = emp
  let ctor_arg_sep = texspace
  let pat_as = tkwd "as"
  let pat_rec_start = kwd "\\Mmagiclrec"
  let pat_rec_end = kwd "\\Mmagicrrec"
  let pat_wildcard = kwd "\\_"

  let const_true = tkwd "true"
  let const_false = tkwd "false"
  let string_quote = r"\""

  let case_start = tkwdl "match"
  let case_sep1 = tkwdm "with"
  let case_sep2 = kwd "|" ^ texspace
  let case_line_sep = kwd "\\rightarrow"
  let case_end = tkwdr "end"
  let cond_if = tkwdl "if"
  let cond_then = tkwdm "then"
  let cond_else = tkwdm "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = tkwdl "fun"
  let fun_sep = kwd "\\rightarrow"
  let function_start = tkwdl "function"
  let function_end = tkwdr "end"
  let record_assign = kwd "="
  let recup_start = kwd "\\Mlrec"
  let recup_middle = texspace ^ kwd "\\Mmagicwith" ^ texspace 
  let recup_end = kwd "\\Mmagicrrec"
  let recup_assign = kwd "="
  let val_start = tkwdl "val"
  let let_start = tkwdl "let"
  let let_in = tkwdm "in"
  let let_end = emp
  let begin_kwd = tkwdl "begin"
  let end_kwd = tkwdr "end"
  let forall = kwd "\\forall"
  let exists = kwd "\\exists"
  let set_quant_binding = kwd "\\mathord{\\in} "
  let list_quant_binding = tkwdm "mem"
  let quant_binding_start = emp (* kwd "("*)
  let quant_binding_end = emp (* kwd ")"*)
  let set_start = kwd "\\{"
  let set_end = kwd "\\}"
  let setcomp_binding_start = kwd "\\forall"
  let setcomp_binding_sep = emp
  let setcomp_binding_middle = texspace ^ kwd "|" ^ texspace
  let setcomp_sep = texspace ^ kwd "|" ^ texspace
  let cons_op = kwd "::"
  let set_sep = kwd ";\\,"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let first_case_sep = Seplist.Optional

  let tup_sep = kwd ",\\,"

  let def_start = tkwdl "let"
  let def_binding = kwd "="
  let def_end = emp
  let def_sep = kwd "|"
  let rec_def_header sk1 sk2 _ = ws sk1 ^ tkwdm "let" ^ ws sk2 ^ tkwdm "rec"
  let rec_def_footer n = emp
  let letbind_sep = kwd "|" ^ texspace 
  let letbind_initial_sep = kwd "|" ^ texspace 
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = tkwdl "indreln"
  let reln_end = emp
  let reln_sep = tkwdm "and"
  let reln_clause_start = kwd "\\forall"
  let reln_clause_end = emp

  let typedef_start = tkwdl "type"
  let typedef_binding = kwd "="
  let typedef_end = emp
  let typedef_sep = tkwdm "and"
  let typedefrec_start = tkwdl "type"
  let typedefrec_end = emp
  let rec_start = kwd "\\Mmagiclrec"
  let rec_end = kwd "\\Mmagicrrec"
  let rec_sep = kwd ";"
  let constr_sep = kwd "*"
  let before_tyvars = emp
  let after_tyvars = emp
  let type_abbrev_start = tkwdl "type"
  let last_rec_sep = Seplist.Optional
  let last_list_sep = Seplist.Optional
  let last_set_sep = Seplist.Optional
  let first_variant_sep = Seplist.Optional
  let type_params_pre = true
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp
  let type_abbrev_name_quoted = false

  let module_module = tkwdl "module"
  let module_struct = tkwdl "struct"
  let module_end = tkwdr "end"
  let module_open = tkwdl "open"

  let some = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"Some"))) Ast.Unknown
  let none = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"None"))) Ast.Unknown
end


module Ocaml : Target = struct
  include Identity 

  let target = Some (Ast.Target_ocaml None)

  let path_sep = kwd "."

  let typ_rec_start = kwd "{"
  let typ_rec_end = kwd "}"

  let ctor_arg_start = kwd "("
  let ctor_arg_end = kwd ")"
  let ctor_arg_sep = kwd ","
  let pat_rec_start = kwd "{"
  let pat_rec_end = kwd "}"
  let pat_wildcard = kwd "_"


  let function_start = kwd "(" ^ kwd "function"
  let function_end = kwd ")"
  let case_start = kwd "(" ^ kwd "match"
  let case_end = kwd ")"
  let recup_start = kwd "{"
  let recup_end = kwd "}"

  let rec_start = kwd "{"
  let rec_end = kwd "}"

  let def_sep = kwd "and"
  let type_params_pre = true
  
end

module Isa : Target = struct
  include Identity 

  let target = Some (Ast.Target_isa None)

  (* TODO : write need_space *)

  let path_sep = kwd "."
  let list_sep = kwd ","

  let typ_start = kwd "\""
  let typ_end = kwd "\""
  let typ_tup_sep = kwd "*"
  let typ_sep = kwd "::"
  let typ_fun_sep = kwd " => "
  let typ_rec_start = kwd "\n"
  let typ_rec_end = kwd "\n"
  let typ_rec_sep = kwd "\n"
  let typ_constr_sep = emp
  let typ_var = r"'"

  let ctor_arg_start = emp
  let ctor_arg_end = emp
  let ctor_arg_sep = emp

  let const_true = kwd "True"
  let const_false = kwd "False"
  let string_quote = r"''"

  let case_start = kwd "(case "
  let case_sep1 = kwd "of"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "=>"
  let case_end = kwd ")"

  let field_access_start = emp
  let field_access_end = kwd " "
  
  let fun_start = kwd "("
  let fun_end = kwd ")"
  let fun_kwd = kwd "%"
  let fun_sep = kwd ". "

  let record_assign = kwd "="
  let recup_start = emp
  let recup_middle = kwd "(|"
  let recup_end = kwd "|)"
  let recup_assign = kwd ":="

  let val_start = kwd "val" (* TODO*)
  let let_start = kwd "(" ^ kwd "let"
  let let_end = kwd ")"

  let begin_kwd = kwd "("
  let end_kwd = kwd ")"
  
  let forall = kwd "ALL"
  let exists = kwd "EX"

  let set_quant_binding = kwd ":"
  let quant_binding_start = emp
  let quant_binding_end = emp

  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = emp
  let setcomp_binding_sep = kwd " "
  let setcomp_binding_middle = kwd "."
  let setcomp_sep = kwd "|"
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")

  let cons_op = kwd "#"
  let set_sep = kwd ","

  let def_start = kwd "definition"
  let def_end = emp

  let def_rec = kwd "fun"
  let def_sep = kwd "|"
  
  let letbind_sep = kwd "|" 
  let letbind_initial_sep = kwd "|"
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "inductive"
  let reln_end = emp
  let reln_sep = kwd "|"
  let reln_clause_start = kwd "\""
  let reln_clause_end = kwd "\""

  let typedef_start = kwd "datatype"
  let typedef_end = emp
  let typedef_sep = kwd "and"

  let typedefrec_start = kwd "record"
  let typedefrec_end = emp
  let rec_start = kwd "(|"
  let rec_end = kwd "|)"
  let rec_sep = kwd ","

  let constr_sep = kwd "\" \""
  let before_tyvars = emp
  let after_tyvars = emp
  let first_variant_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_list_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_rec_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_set_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let type_abbrev_start = kwd "type_synonym"
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp

end

let back_tick = List.hd (Ulib.Text.explode (r"`"))

module Hol : Target = struct
  open Str

  let lex_skip = function
    | Ast.Com(r) -> 
        (*
        Ulib.Text.replace 
          (fun c -> 
             if c = back_tick then 
               (* TODO: Use ^` instead? *)
               Ulib.Text.to_ustring (r"REPLACED BACKQUOTE") 
             else 
               BatUTF8.of_char c)
         *)
          (ml_comment_to_rope r)
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  (* TODO: These join up :- -> *, *)
  let delim_regexp = regexp "^\\([][(){}~.,;-]\\)$"

  let symbolic_regexp = regexp "^[!%&*+/:<=>?@^|#\\`]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = 
    let f x =
      match x with
        | Kwd'(s) ->
            if is_delim s then
              (true,false)
            else if is_symbolic s then
              (false,true)
            else
              (false,false)
        | Ident'(r) ->
            (false, is_symbolic (Ulib.Text.to_string r))
        | Num' _ ->
            (false,false)
    in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2

  let target = Some (Ast.Target_hol None)

  let path_sep = kwd "$"
  let list_sep = kwd ";"

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "#"
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "->"
  let typ_rec_start = kwd "<|"
  let typ_rec_end = kwd "|>"
  let typ_rec_sep = kwd ";"
  let typ_constr_sep = kwd "of"
  let typ_var = r"'"

  let ctor_arg_start = emp
  let ctor_arg_end = emp
  let ctor_arg_sep = emp
  let pat_as = err "as pattern in HOL"
  let pat_rec_start = err "record pattern in HOL"
  let pat_rec_end = err "record pattern in HOL"
  let pat_wildcard = kwd "_"

  let const_true = kwd "T"
  let const_false = kwd "F"
  let string_quote = r"\""

  let function_start = err "function in HOL"
  let function_end = err "function in HOL"
  let case_start = kwd "(" ^ kwd "case"
  let case_sep1 = kwd "of"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "=>"
  let case_end = kwd ")"
  let cond_if = kwd "if"
  let cond_then = kwd "then"
  let cond_else = kwd "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = kwd "\\"
  let fun_sep = kwd "."
  let record_assign = kwd ":="
  let recup_start = emp
  let recup_middle = kwd "with" ^ kwd "<|"
  let recup_end = kwd "|>"
  let recup_assign = kwd ":="
  let val_start = err "val specification in HOL"
  let let_start = kwd "let"
  let let_in = kwd "in"
  let let_end = emp
  let begin_kwd = kwd "("
  let end_kwd = kwd ")"
  let forall = kwd "!"
  let exists = kwd "?"
  let list_quant_binding = err "list restricted quantifier in HOL"
  let set_quant_binding = kwd "::"
  let quant_binding_start = kwd "("
  let quant_binding_end = kwd ")"
  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = emp
  let setcomp_binding_sep = kwd ","
  let setcomp_binding_middle = kwd "|"
  let setcomp_sep = kwd "|"
  let cons_op = kwd "::"
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")

  let tup_sep = kwd ","

  let def_start = meta "val _ = Define `\n"
  let def_binding = kwd "="
  let def_end = meta "`;\n"
  let def_sep = kwd "/\\"
  let rec_def_header sk1 sk2 n = 
    ws sk1 ^ ws sk2 ^ 
    let n = Ulib.Text.to_string (Name.to_rope n) in 
      meta (Format.sprintf "val %s_defn = Hol_defn \"%s\" `\n" n n)
  let rec_def_footer n =
    meta (Format.sprintf "\nval _ = Defn.save_defn %s_defn;" 
            (Ulib.Text.to_string (Name.to_rope n)))

  let letbind_sep = kwd "/\\" 
  let letbind_initial_sep = space
  let funcase_start = kwd "("
  let funcase_end = kwd ")"
  let reln_start = meta "val _ = Hol_reln `"
  let reln_end = meta "`;"
  let reln_sep = kwd "/\\"
  let reln_clause_start = kwd "(" ^ kwd "!"
  let reln_clause_end = kwd ")"

  let typedef_start = meta "val _ = Hol_datatype `\n"
  let typedef_binding = kwd "="
  let typedef_end = meta "`;\n"
  let typedef_sep = kwd ";"
  let typedefrec_start = meta "val _ = Hol_datatype `\n"
  let typedefrec_end = meta "`;\n"
  let rec_start = kwd "<|"
  let rec_end = kwd "|>"
  let rec_sep = kwd ";"
  let constr_sep = kwd "=>"
  let before_tyvars = kwd "(*" ^ space
  let after_tyvars = space ^ kwd "*)"
  let last_rec_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_list_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_set_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let first_variant_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let type_params_pre = true
  let type_abbrev_start = meta "val _ = type_abbrev("
  let type_abbrev_sep = meta ", ``:"
  let type_abbrev_end = meta "``);"
  let type_abbrev_name_quoted = true

  let module_module = kwd "module"
  let module_struct = kwd "struct"
  let module_end = kwd "end"
  let module_open = kwd "open"

  let some = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"SOME"))) Ast.Unknown
  let none = Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"NONE"))) Ast.Unknown

end

module Coq : Target = struct
  open Str
  include Identity

  let need_space x y = 
    let sx =
      match x with
      | Kwd'(r) ->
          if String.compare r "fun" = 0 then true else
          if String.compare r "match" = 0 then true else
          false
      | _ -> false in
    let sy =
      match y with
      | Kwd'(r) ->
          if String.compare r "end" = 0 then true else 
          false
      | _ -> false in
    sx || sy

  let target = Some (Ast.Target_coq None)

  let list_sep = kwd "::"

  let path_sep = kwd "."

  (* Types *)

  let typ_start = kwd "("
  let typ_end = kwd ")%type"

  let typ_rec_start = kwd "{"
  let typ_rec_end = kwd "}"
  let typ_rec_sep = kwd ";"
  let typ_constr_sep = kwd ":"
  let typ_var = r""

  (* Patterns *)

  (* Constants *)

  (* Expressions *)
  let case_line_sep = kwd "=>"
  let cond_if = kwd "if"
  let cond_then = kwd "then"
  let cond_else = kwd "else"
  let field_access_start = kwd ".("
  let field_access_end = kwd ")"
  let fun_sep = kwd "=>"
  let begin_kwd = kwd "("
  let end_kwd = kwd ")"
  let list_begin = emp
  let list_end = kwd "nil"

  (* Value definitions *)
  let def_start = kwd "Definition"
  let def_binding = kwd ":="
  let def_end = kwd "."


  (* Type definitions *)
  let type_abbrev_start = kwd "Definition" 
  let typedef_start = kwd "Inductive"
  let typedef_binding = kwd ":="
  let typedef_end = kwd "."
  let typedef_sep = kwd "with"
  let typedefrec_start = kwd "Record"
  let typedefrec_end = kwd "."
  (* let rec_start = kwd "{" *)
  (* let rec_end = kwd "}" *)
  (* let rec_sep = kwd ";" *)
  let constr_sep = kwd "->"

  let last_list_sep = Seplist.Require(None)
  let type_params_pre = false
  let type_abbrev_start = kwd "Definition"
  let type_abbrev_sep = kwd ":="
  let type_abbrev_end = kwd "."

end


module F(T : Target)(C : Exp_context)(X : sig val comment_def : def -> Ulib.Text.t end) = struct

module C = Exps_in_context(C)

let rec interspace os = 
  match os with
  | [] -> [emp]
  | [x] -> [x]
  | x::((_::_) as os') -> x:: texspace:: interspace os'

let sep x s = ws s ^ x

let bracket_many f s b1 b2 l =
  match l with
    | [] -> emp
    | [t] -> f t
    | (t::ts) -> 
        (* Put the parenthesis right before the first type *)
        let (t', sk) = typ_alter_init_lskips (fun (s) -> (None,s)) t in
          ws sk ^ b1 ^ concat s (List.map f (t'::ts))  ^ b2


let lit l = match l.term with
  | L_true(s) -> ws s ^ T.const_true
  | L_false(s) -> ws s ^ T.const_false
  | L_num(s,i) -> ws s ^ num i
  | L_string(s,i) -> ws s ^ str (Ulib.Text.of_latin1 i)
  | L_unit(s1,s2) -> ws s1 ^ kwd "(" ^ ws s2 ^ kwd ")"


(* TODO: PB: Hack to get rid of the "Pervasive." when the option type contrucor
* is printed. *)
let typ_ident_to_output p =     
  let id = 
    if Path.compare p.descr 
        (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"option"))) = 0 
    then  Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r"option"))) Ast.Unknown
    else p.id_path
  in Ident.to_output Type_ctor T.path_sep id


let rec typ t = match t.term with
  | Typ_wild(s) ->
      ws s ^ kwd "_"
  | Typ_var(s,v) ->
      ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var (Tyvar.to_rope v))
  | Typ_fn(t1,s,t2) ->
      typ t1 ^
      ws s ^
      T.typ_fun_sep ^
      typ t2
  | Typ_tup(ts) ->
      flat (Seplist.to_sep_list typ (sep T.typ_tup_sep) ts)
  | Typ_app(p, ts) ->
      if T.type_params_pre then
        bracket_many typ (T.tup_sep) (kwd "(") (kwd ")") ts ^
        texspace ^ (typ_ident_to_output p)
      else
        (* FZ again, slightly distasteful: we know that the backend is *)
        (* Coq and we do not print parentheses; however parentheses *)
        (* should be parametrised *)
       (Ident.to_output Type_ctor T.path_sep p.id_path) ^
        flat (List.map typ ts)
        
  | Typ_paren(s1,t,s2) ->
      ws s1 ^
      kwd "(" ^
      typ t ^
      ws s2 ^
      kwd ")"



let ctor_ident_to_output cd =
  (* TODO: remove this hack *)
  let id = 
    if Path.compare cd.descr.constr_binding 
         (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"None"))) = 0 then
      Ident.replace_first_lskip T.none (Ident.get_first_lskip cd.id_path)
    else if Path.compare cd.descr.constr_binding 
              (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"Some"))) = 0 then
      Ident.replace_first_lskip T.some (Ident.get_first_lskip cd.id_path)
    else
      cd.id_path
  in
    Ident.to_output Term_ctor T.path_sep id


let const_ident_to_output cd =
  (* TODO: remove this hack *)
  match T.target with
  | Some (Ast.Target_tex _) -> 
      if      Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"union"))) = 0 then kwd "\\cup"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"inter"))) = 0 then kwd "\\cap"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"IN")))    = 0 then kwd "\\in"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"&&")))    = 0 then kwd "\\lemwedge"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"||")))    = 0 then kwd "\\lemvee"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"not")))   = 0 then kwd "\\lemnot"
      else
        Ident.to_output Term_const T.path_sep cd.id_path
  | Some (Ast.Target_html _) -> 
      if      Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"union"))) = 0 then kwd "&cup;" 
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"inter"))) = 0 then kwd "^cap;"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"-->")))    = 0 then kwd "&rarr;"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"IN")))    = 0 then kwd "&isin;"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"&&")))    = 0 then kwd "&amp;&amp;"
(*
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"||")))    = 0 then kwd "\\lemvee"
      else if Path.compare cd.descr.const_binding (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"not")))   = 0 then kwd "\\lemnot"
*)
      else
        Ident.to_output Term_const T.path_sep cd.id_path
  | _ -> 
        Ident.to_output Term_const T.path_sep cd.id_path





  
let rec pat p = match p.term with
  | P_wild(s) ->
      ws s ^
      T.pat_wildcard

  | P_as(s1,p,s2,(n,l),s3) ->
      ws s1 ^ 
      pat p ^
      ws s2 ^ 
      T.pat_as ^
      Name.to_output Term_var n ^
      ws s3

  | P_typ(s1,p,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      pat p ^
      ws s2 ^
      T.typ_sep ^
      typ t ^
      ws s3 ^
      kwd ")"

  | P_var(n) ->
      Name.to_output Term_var n

  | P_constr(cd,ps) ->
      (* TODO: do we need to check the internal kind of cd (ctor/let)? *)
      ctor_ident_to_output cd ^
      begin
        match ps with
          | [] ->
              emp
          | _ ->
              texspace ^ 
              T.ctor_arg_start ^
              concat T.ctor_arg_sep (List.map pat ps) ^
              T.ctor_arg_end
      end

  | P_record(s1,fields,s2) ->
      ws s1 ^
      T.pat_rec_start ^
      flat (Seplist.to_sep_list patfield (sep T.rec_sep) fields) ^
      ws s2 ^
      T.pat_rec_end

  | P_tup(s1,ps,s2) ->
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list pat (sep T.tup_sep) ps) ^
      ws s2 ^
      kwd ")"

  | P_list(s1,ps,s2) ->
      ws s1 ^
      T.list_begin ^
      flat 
        (Seplist.to_sep_list_last T.last_list_sep 
           pat (sep T.list_sep) ps) ^
      ws s2 ^
      T.list_end

  | P_paren(s1,p,s2) ->
      ws s1 ^
      kwd "(" ^
      pat p ^
      ws s2 ^
      kwd ")"

  | P_cons(p1,s,p2) ->
      pat p1 ^ 
      ws s ^
      T.cons_op ^
      pat p2

  | P_lit(l) ->
      lit l

  | P_var_annot(n,t) ->
      kwd "(" ^
      Name.to_output Term_var n ^
      T.typ_sep ^
      typ t ^
      kwd ")"


and patfield (fd,s1,p) =
  Ident.to_output Term_field T.path_sep fd.id_path ^
  ws s1 ^
  kwd "=" ^
  pat p

and patlist ps = 
  match ps with
  | [] -> emp
  | [p] -> pat p
  | p::((_::_) as ps') -> pat p ^ texspace ^ patlist ps'

let rec exp e = match C.exp_to_term e with
  | Var(n) ->
      Name.to_output Term_var n

  | Constant(cd) ->
      const_ident_to_output cd (*Ident.to_output Term_const T.path_sep cd.id_path*)

  | Constructor(cd) ->
      ctor_ident_to_output cd

  | Tup_constructor(cd,s1,es,s2) ->
      Ident.to_output Term_ctor T.path_sep cd.id_path ^
      ws s1 ^
      (if Seplist.length es = 0 then
         ws s2
       else
         kwd "(" ^
         flat (Seplist.to_sep_list exp (sep T.tup_sep) es) ^
         ws s2 ^
         kwd ")")

  | Fun(s1,ps,s2,e) ->
      ws s1 ^
      T.fun_start ^
      T.fun_kwd ^
      patlist ps ^
      ws s2 ^
      T.fun_sep ^
      exp e ^
      T.fun_end

  | Function(s1,f,s2) ->
      ws s1 ^
      T.function_start ^
      flat (Seplist.to_sep_list 
              (fun (p,s1,e,l) ->
                 pat p ^
                 ws s1 ^
                 T.fun_sep ^
                 exp e) 
              (sep (kwd "|"))
              f) ^
        ws s2 ^
      T.function_end

  | App(e1,e2) ->
      exp e1 ^
      texspace ^
      exp e2

  | Infix(e1,e2,e3) ->
      exp e1 ^
      texspace ^ 
      exp e2 ^
      texspace ^ 
      exp e3

  | Record(s1,fields,s2) ->
      ws s1 ^
      T.rec_start ^
      flat 
        (Seplist.to_sep_list_last 
           T.last_rec_sep 
           expfield (sep T.rec_sep) fields) ^
      ws s2 ^
      T.rec_end

  | Record_coq((n,l),s1,fields,s2) ->
      ws s1 ^
      Name.to_output Term_field n ^
      flat 
        (Seplist.to_sep_list_last 
           T.last_rec_sep 
           expfield_coq (fun s -> ws s) fields) ^
      ws s2 


  | Recup(s1,e,s2,fields,s3) ->
      ws s1 ^
      T.recup_start ^
      exp e ^
      ws s2 ^
      T.recup_middle ^ 
      flat 
        (Seplist.to_sep_list_last 
           T.last_rec_sep 
           expfieldup (sep T.rec_sep) fields) ^
      ws s3 ^
      T.recup_end

  | Field(e,s,fd) ->
      if (T.target = Some (Ast.Target_isa None)) then
        T.field_access_start ^ 
        Ident.to_output Term_field T.path_sep fd.id_path ^
        T.field_access_end ^ 
        exp e ^ 
        ws s
      else 
        exp e ^
        ws s ^
        T.field_access_start ^
        Ident.to_output Term_field T.path_sep fd.id_path ^
        T.field_access_end

  | Case(s1,e,s2,cases,s3) ->
      ws s1 ^
      T.case_start ^
      exp e ^
      ws s2 ^
      T.case_sep1 ^
      flat 
        (Seplist.to_sep_list_first 
           T.first_case_sep case_line 
           (sep T.case_sep2)
           cases) ^
      ws s3 ^
      T.case_end

  | Typed(s1,e,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      exp e ^
      ws s2 ^
      T.typ_sep ^
      typ t ^
      ws s3 ^
      kwd ")"

  | Let(s1,bind,s2,e) ->
      ws s1 ^
      T.let_start ^
      letbind Types.TVset.empty bind ^
      ws s2 ^
      T.let_in ^
      exp e ^
      T.let_end

  | Tup(s1,es,s2) ->
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list exp (sep T.tup_sep) es) ^
      ws s2 ^
      kwd ")"

  | List(s1,es,s2) ->
      ws s1 ^
      T.list_begin ^
      flat 
        (Seplist.to_sep_list_last T.last_list_sep 
           exp (sep T.list_sep) es) ^
      ws s2 ^
      T.list_end

  | Paren(s1,e,s2) ->
      ws s1 ^ kwd "(" ^ exp e ^ ws s2 ^ kwd ")"

  | Begin(s1,e,s2) ->
      ws s1 ^ T.begin_kwd ^ exp e ^ ws s2 ^ T.end_kwd

  | If(s1,e1,s2,e2,s3,e3) ->
      ws s1 ^
      T.cond_if ^
      exp e1 ^
      ws s2 ^
      T.cond_then ^
      exp e2 ^
      ws s3 ^
      T.cond_else ^
      exp e3

  | Lit(l) ->
      lit l

  | Set(s1,es,s2) -> 
      ws s1 ^
      T.set_start ^
      flat 
        (Seplist.to_sep_list_last 
           T.last_set_sep 
           exp (sep T.set_sep) es) ^
      ws s2 ^
      T.set_end

  (* TODO: Add an isabelle transformation from Setcomp to
   * Comp_binding(false,...) *)
  | Setcomp(s1,e1,s2,e2,s3,vars) ->
      ws s1 ^
      T.set_start ^
      exp e1 ^
      ws s2 ^
      T.setcomp_sep ^
      (if T.target = Some (Ast.Target_isa(None)) then 
         flat (List.map (fun x -> id Term_var (Name.to_rope x)) (NameSet.elements vars)) ^
         T.setcomp_binding_middle 
       else 
         emp) ^
      exp e2 ^
      ws s3 ^
      T.set_end

  (* List comprehensions *)
  | Comp_binding(true,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      ws s1 ^
      kwd "[" ^
      exp e1 ^
      ws s2 ^
      kwd "|" ^
      ws s5 ^
      T.setcomp_binding_start ^
      concat T.setcomp_binding_sep (List.map quant_binding qbs) ^
      ws s3 ^
      T.setcomp_binding_middle ^ 
      exp e2 ^
      ws s4 ^
      kwd "]"

  (* Set comprehensions *)
  | Comp_binding(false,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      ws s1 ^
      T.set_start ^
      exp e1 ^
      ws s2 ^
      kwd "|" ^
      ws s5 ^
      T.setcomp_binding_start ^
      concat T.setcomp_binding_sep (List.map quant_binding qbs) ^
      ws s3 ^
      T.setcomp_binding_middle ^ 
      exp e2 ^
      ws s4 ^
      T.set_end

  (* TODO: Add an Isabelle transformation to nested Quants *)
  | Quant(q,qbs,s2,e) ->
      if (T.target = Some (Ast.Target_isa None)) then 
        kwd "(" ^ 
        flat (List.map (isa_quant q) qbs) ^
        ws s2 ^ exp e ^ 
        kwd ")"
      else 
        begin
          match q with
          | Ast.Q_forall(s1) ->
              ws s1 ^ T.forall
          | Ast.Q_exists(s1) ->
              ws s1 ^ T.exists
        end ^
        flat (interspace (List.map quant_binding qbs)) ^
        ws s2 ^
        kwd "." ^
        texspace ^
        exp e
          
and quant_binding = function
  | Qb_var(n) -> 
      Name.to_output Term_var n.term
  | Qb_restr(is_lst,s1,p,s2,e,s3) ->
      ws s1 ^
      T.quant_binding_start ^
      pat p ^
      ws s2 ^
      (if is_lst then T.list_quant_binding else T.set_quant_binding) ^
      exp e ^
      ws s3 ^
      T.quant_binding_end

and isa_quant q qb = match q with
  | Ast.Q_forall(s1) -> 
      ws s1 ^ T.forall ^ (quant_binding qb) ^ kwd "." ^ space
  | Ast.Q_exists(s1) ->
      ws s1 ^ T.exists ^ (quant_binding qb) ^ kwd "." ^ space

and expfield (fd,s1,e,_) =
  Ident.to_output Term_field T.path_sep fd.id_path ^
  ws s1 ^
  T.record_assign ^
  exp e

and expfield_coq (fd,s1,e,_) =
  ws s1 ^
  exp e

and expfieldup (fd,s1,e,_) =
  Ident.to_output Term_field T.path_sep fd.id_path ^
  ws s1 ^
  T.recup_assign ^
  exp e

and case_line (p,s1,e,_) =
  pat p ^
  ws s1 ^
  T.case_line_sep ^
  exp e

and coq_tyvar_binding tvs =
  if T.target = Some (Ast.Target_coq None) then
    flat (List.map 
            (fun tv -> 
               kwd"(" ^ 
               id Type_var (Ulib.Text.(^^^) T.typ_var (Tyvar.to_rope tv)) ^ 
               meta ":Type" ^ 
               kwd ")") 
            (Types.TVset.elements tvs))
  else 
    emp

and funcl tvs ({term = n}, ps, topt, s1, e) =
  ws (Name.get_lskip n) ^ 
  T.funcase_start ^
  Name.to_output Term_var (Name.replace_lskip n None) ^
  coq_tyvar_binding tvs ^
  (match ps with [] -> emp | _ -> texspace) ^
  patlist ps ^
  begin
    match topt with
      | None -> emp 
      | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
  end ^
  ws s1 ^
  T.def_binding ^
  exp e ^
  T.funcase_end
    
and letbind tvs (lb, _) : Output.t = match lb with
  | Let_val(p,topt,s2,e) ->
      pat p ^ 
      coq_tyvar_binding tvs ^
      begin
        match topt with
          | None -> emp 
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
      end ^
      ws s2 ^ T.def_binding ^ exp e
  | Let_fun(clause) ->
      funcl tvs clause

let tyvar (s, tv, l) =
  ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var tv)

let tyfield ((n,l),s1,t) =
  Name.to_output Term_field n ^
  ws s1 ^
  T.typ_sep ^
  T.typ_start ^
  typ t ^
  T.typ_end

let tyconstr ((n,l),s1,targs) =
  Name.to_output Type_ctor n ^
  ws s1 ^
  (if Seplist.length targs = 0 then
     emp 
   else
     T.typ_constr_sep ^
     T.typ_start ^
     flat (Seplist.to_sep_list typ (sep T.constr_sep) targs) ^
     T.typ_end)

let tyconstr_coq ((n,l),s1,targs,(n1,l1),tvs) =
  Name.to_output Type_ctor n ^
  ws s1 ^
  (if Seplist.length targs = 0 then
     emp 
   else
     T.typ_constr_sep ^
     T.typ_start ^
     flat (Seplist.to_sep_list typ (sep T.constr_sep) targs) ^
     T.constr_sep ^ Name.to_output Type_ctor n1 ^ space ^
     (flat (List.map tyvar tvs)) ^ (* FZ discharging comments here *)
     T.typ_end)
    
let tyexp_abbrev s4 t =
  ws s4 ^
  T.type_abbrev_sep ^
  T.typ_start ^
  typ t ^
  T.typ_end

let tyexp_rec s4 s5 fields s6 =
  ws s4 ^
  T.typedef_binding ^
  ws s5 ^
  T.typ_rec_start ^
  flat (Seplist.to_sep_list_last 
          T.last_rec_sep 
          tyfield 
          (sep T.typ_rec_sep) 
          fields) ^
  ws s6 ^
  T.typ_rec_end

let tyexp = function
  | Te_opaque -> 
      emp
  
  | Te_abbrev(s,t) ->
      tyexp_abbrev s t
  
  | Te_record(s3, s1, fields, s2) ->
      tyexp_rec s3 s1 fields s2

  | Te_record_coq(s3, (n,l), s1, fields, s2) ->
      ws s3 ^ 
      T.typedef_binding ^
      Name.to_output Type_ctor n ^
      ws s1 ^
      T.typ_rec_start ^
      flat (
        Seplist.to_sep_list
        tyfield (sep T.typ_rec_sep) fields
        ) ^
      ws s2 ^
      T.typ_rec_end
  
  | Te_variant(s,constrs) ->
      ws s ^
      T.typedef_binding ^
      flat (Seplist.to_sep_list_first 
              T.first_variant_sep
              tyconstr
              (sep (texspace ^ kwd "|" ^ texspace))
              constrs)

  | Te_variant_coq(s,constrs) ->
      ws s ^
      T.typedef_binding ^
      flat (
        Seplist.to_sep_list_first 
          T.first_case_sep
          tyconstr_coq
          (sep (kwd "|"))
          constrs
        )


(* In Isabelle we have to handle the following three cases for type definitions
 * separately: 
 * - record types have to be defined usind the record keyword
 * - simple type aliases like type time = num are handled using the types
 *   keyword
 * - Types with constuctors like type t = a | b are introduced using the
 *   datatype keyword
let tdef_start = function 
  | Te_opaque ->
      T.typedef_start
  | Te_abbrev(_,_) ->
      T.type_abbrev_start 
  | Te_record(_,_,_,_) ->
      T.typedefrec_start 
  | Te_record_coq(_,_,_,_,_) ->
      T.typedefrec_start 
  | Te_variant(_,_) ->
      T.typedef_start  
  | Te_variant_coq(_,_) ->
      T.typedef_start  
 *)   

let tdef_tvars ml_style tvs = 
  match tvs with
    | [] -> emp
    | [tv] ->
        T.before_tyvars ^
        tyvar tv ^
        T.after_tyvars
    | tvs ->
        let s = if ml_style then T.tup_sep else emp in
          T.before_tyvars ^
          (if ml_style then kwd "(" else emp) ^
          flat (Seplist.to_sep_list tyvar (sep s) (Seplist.from_list (List.map (fun tv -> (tv,None)) tvs))) ^
          (if ml_style then kwd ")" else emp) ^
          T.after_tyvars

let tdef_tctor quoted_name tvs n =
  let nout = 
    if quoted_name then Name.to_output_quoted Type_ctor n else Name.to_output Type_ctor n 
  in
    if T.type_params_pre then
      tdef_tvars true tvs ^
      nout 
    else
      (* FZ slightly distasteful: in this case we know that the backend *)
      (* is Coq and we do not print parentheses; however parentheses *)
      (* should be parametrised *)
      nout ^
      tdef_tvars false tvs

let tdef ((n,l), tvs, texp) =
  tdef_tctor false tvs n ^
  tyexp texp

let indreln_clause (s1, qnames, s2, e, s3, rname, es) =
  ws s1 ^
  T.reln_clause_start ^
  flat (interspace (List.map (fun n -> Name.to_output Term_var n.term) qnames)) ^
  ws s2 ^
  kwd "." ^
  exp e ^
  ws s3 ^
  kwd "==>" ^
  Name.to_output Term_var rname.term ^
  flat (interspace (List.map exp es)) ^
  T.reln_clause_end

let targets_opt = function
  | None -> emp
  | Some((s1,targets,s2)) ->
      ws s1 ^
      T.set_start ^
      flat (Seplist.to_sep_list (target_to_output Target) (sep T.set_sep) targets) ^
      ws s2 ^
      T.set_end

let in_target targs = 
  match (T.target,targs) with
    | (None,_) -> true
    | (_,None) -> true
    | (Some(t), Some((_,targets,_))) ->
        Seplist.exists (fun t' -> ast_target_compare t t' = 0) targets


(****** Isabelle ******)

let isa_op_typ texp = match texp.term with
  | Typ_fn(_,_,_) -> kwd "[" ^ typ texp ^ kwd "]"
  | _ -> typ texp


(* let quote_ident name = match (name : Output.t) with 
*)

(* isa_mk_typed_def_header:
 * generates the Isar 'name-type' line of the form 
 *      name :: "type" where \n
 * for each top-level definition name, we check whether it is a isa(r) keyword
 * and in case it is, we put the name in double quotes.
 * isa-keywords is defined in isa_keyowrds.ml
*)

let isa_mk_typed_def_header (name, ptyps, s, etyp) : Output.t = 
  name ^ kwd " " ^ T.typ_sep ^ kwd " \"" ^ 
  flat (List.map (function x -> isa_op_typ (C.t_to_src_t x) ^ T.typ_fun_sep) ptyps) ^
  typ (C.t_to_src_t etyp) ^ 
  kwd "\" " ^ ws s ^ kwd "where \n"

(*
  flat (List.map (function x -> (isa_op_typ (C.t_to_src_t x.typ) ^ 
  if es=[] then emp else T.typ_fun_sep)) ps) ^
  flat (List.map (function ex -> typ (C.t_to_src_t (exp_to_typ ex))) es) ^ 
*)

let isa_funcl eqsign ({term = n}, ps, topt, s1, (e : Typed_ast.exp)) =
  isa_mk_typed_def_header (Name.to_output Term_var n, List.map Typed_ast.annot_to_typ ps, s1, exp_to_typ e) ^
  kwd "\"" ^ Name.to_output Term_var n ^ flat (List.map pat ps)^ ws s1 ^ eqsign ^ exp e ^ kwd "\""

let isa_letbind (lb, _) : Output.t = match lb with  
  | Let_val(p,topt,s2,e) ->
      isa_mk_typed_def_header (pat p,[],s2, exp_to_typ e) ^
      kwd "\"" ^ pat p ^ ws s2 ^ kwd "== " ^ exp e ^ kwd "\""
  | Let_fun(clause) ->
      isa_funcl (kwd "== ") clause

let isa_indreln_clause (s1, qnames, s2, e, s3, rname, es) =
  ws s1 ^ T.reln_clause_start ^
  ws s2 ^ exp e ^
  ws s3 ^ kwd "==>" ^
  Name.to_output Term_var rname.term ^
  flat (interspace (List.map exp es)) ^
  T.reln_clause_end

(******* End Isabelle ********)

let constraints = function
  | None -> emp
  | Some(Cs_list(l,s)) ->
      flat (Seplist.to_sep_list
              (fun (id,tv) ->
                 Ident.to_output Type_var T.path_sep id ^
                 tyvar tv)
              (sep (kwd","))
              l) ^
      ws s ^
      kwd "=>"



let constraint_prefix (Cp_forall(s1,tvs,s2,constrs)) =
  ws s1 ^
  T.forall ^
  flat (List.map tyvar tvs) ^
  ws s2 ^
  kwd "." ^
  constraints constrs

let is_abbrev l = 
  Seplist.length l = 1 &&
  match Seplist.hd l with
    | (_,_,Te_abbrev _) -> true
    | _ -> false

let is_rec l = 
  Seplist.length l = 1 &&
  match Seplist.hd l with
    | (_,_,Te_record _) -> true
    | _ -> false


let rec def d : Output.t = match d with

  (* A single type abbreviation *)
  | Type_def(s1, l) when is_abbrev l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,Te_abbrev(s4,t)) ->
              ws s1 ^
              T.type_abbrev_start ^
              tdef_tctor T.type_abbrev_name_quoted tvs n ^
              tyexp_abbrev s4 t ^
              T.type_abbrev_end
          | _ -> assert false
      end

  (* A single record definition *)
  | Type_def(s1, l) when is_rec l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,Te_record(s4,s5,fields,s6)) ->
              ws s1 ^
              T.typedefrec_start ^
              tdef_tctor false tvs n ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end
          | _ -> assert false
      end

  | Type_def(s, defs) ->
      ws s ^
      T.typedef_start ^
      flat (Seplist.to_sep_list tdef (sep T.typedef_sep) defs) ^
      T.typedef_end

  | Val_def(Let_def(s1, targets,bind),tvs) -> 
      if in_target targets then
        ws s1 ^
        T.def_start ^
        (if T.target = None then
           targets_opt targets 
         else
           emp) ^
        letbind tvs bind ^
        T.def_end
      else
        emp
  | Val_def(Rec_def(s1, s2, targets, clauses),tvs) -> 
      if in_target targets then
        let n = 
          match Seplist.to_list clauses with
            | [] -> assert false
            | (n, _, _, _, _)::_ -> Name.strip_lskip n.term
        in
          T.rec_def_header s1 s2 n ^
          (if T.target = None then
             targets_opt targets 
           else
             emp) ^
          flat (Seplist.to_sep_list (funcl tvs) (sep T.def_sep) clauses) ^
          T.def_end ^
          T.rec_def_footer n
          else
        emp
  | Val_def(Let_inline(s1,s2,targets,n,args,s4,body),tvs) ->
      if (T.target = None) then
        ws s1 ^
        kwd "let" ^
        ws s2 ^
        kwd "inline" ^
        targets_opt targets ^
        Name.to_output Term_var n.term ^
        flat (List.map (fun n -> Name.to_output Term_var n.term) args) ^ 
        ws s4 ^
        kwd "=" ^
        exp body
      else
        emp
  | Module(s1,(n,l),s2,s3,ds,s4) -> 
      ws s1 ^
      T.module_module ^
      Name.to_output Module_name n ^
      ws s2 ^
      kwd "=" ^
      ws s3 ^
      T.module_struct ^
      defs ds ^
      ws s4 ^
      T.module_end
  | Rename(s1,(n,l),s2,m) ->
      ws s1 ^
      T.module_module ^
      Name.to_output Module_name n ^
      ws s2 ^
      kwd "=" ^
      Ident.to_output Module_name T.path_sep m.id_path
  | Open(s,m) ->
      ws s ^
      T.module_open ^
      Ident.to_output Module_name T.path_sep m.id_path
  | Indreln(s,targets,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        (if T.target = None then
           targets_opt targets 
         else
           emp) ^
        flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp
  | Val_spec(s1,(n,l),s2,(constraint_pre,t)) ->
      ws s1 ^
      T.val_start ^
      Name.to_output Term_var n ^
      ws s2 ^
      T.typ_sep ^
      begin
        match constraint_pre with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      typ t
  | Instance(s1,(cp,s2,id,t,s3),methods,s4,e_v,name) ->
      ws s1 ^
      kwd "instance" ^
      begin
        match cp with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      ws s2 ^
      kwd "(" ^
      Ident.to_output Term_method T.path_sep id ^
      typ t ^
      ws s3 ^
      kwd ")" ^
      flat (List.map (fun d -> def (Val_def(d,Types.TVset.empty))) methods) ^
      ws s4 ^
      kwd "end"
  | Class(s1,s2,(n,l), tv, s3, specs, s4) -> 
      ws s1 ^
      kwd "class" ^
      ws s2 ^
      kwd "(" ^
      Name.to_output Class_name n ^
      tyvar tv ^
      ws s3 ^
      kwd ")" ^
      flat (List.map 
              (fun (s1,(n,l),s2,t) ->
                ws s1 ^
                T.val_start ^
                Name.to_output Term_method n ^
                ws s2 ^
                kwd ":" ^
                typ t)
              specs) ^
      ws s4 ^
      kwd "end"
  | Comment(d) ->
      let (d',sk) = def_alter_init_lskips (fun sk -> (None, sk)) d in
        ws sk ^ ws (Some([Ast.Com(Ast.Comment([Ast.Chars(X.comment_def d')]))]))



(* for -inc.tex definitions *)


(*  latex scheme: for a top level function definition of set_option_map, we'll generate:

\newcommand{\setToptionTmap}{             latex command name
\lemdefn
{lab:setToptionTmap}                #1 latex label
{set\_option\_map}                  #2 typeset name (eg to go in index and contents line) 
{A set option map}                  #3 immediately-preceding comment
{\lemfoo{let} \ }                   #4 the left-hand-side keyword (let, type, module,...) 
{\lemfoo{set\_option\_map} \;\tsunknown{f} \;\tsunknown{xs} = {}\\{}}    #5 left hand side
{\{ (\Mcase  \;\tsunknown{f} \;\tsunknown{x} \;\Mof ...  }               #6 rhs 
{That was a set option map}         #7 immediately-following comment
}

The immediately-preceding comment is a preceding (** *) comment (if
  any) that is not separated by more than a single newline and
  spaces/tabs from this definition.
The immediately-following comment is similar. 
The typeset name should already have any tex hom applied.
The left hand side keyword, and the left hand side, should include any
  following newlines (and comments before them?) so that the rhs is
  clean.  
The concatentation of the lhs keyword, the lhs, and the rhs should be exactly what we
  print in whole-document mode (minus the "\lemdef" there).  Modulo the pre/post comments...
*)


and make_lemdefn latex_name latex_label typeset_name pre_comment lhs_keyword lhs rhs post_comment = 
  (r"\\newcommand{" ^^^^ latex_name ^^^^ r"}{%\n" ^^^^
  r"\\lemdefn\n" ^^^^ 
  r"{" ^^^^ latex_label ^^^^ r"}\n" ^^^^
  r"{" ^^^^ typeset_name ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ pre_comment ^^^^ r"}\n" ^^^^
  r"{" ^^^^ lhs_keyword ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ lhs ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ rhs ^^^^ r"}\n" ^^^^
  r"{" ^^^^ post_comment ^^^^ r"}%\n" ^^^^
  r"}\n",
  latex_name ^^^^ r"\n")
 


(* keep locations for latex-name-clash error reporting... *)

and names_of_pat p : (Ulib.Text.t * Ulib.Text.t * Ast.l) list = match p.term with
  | P_wild(s) ->
      []
  | P_as(s1,p,s2,(n,l),s3) ->
      let n' = Name.strip_lskip n in 
      names_of_pat p  @ [(Name.to_rope n',Name.to_rope_tex Term_var n', p.locn)]
  | P_typ(s1,p,s2,t,s3) ->
      names_of_pat p
  | P_var(n) | P_var_annot(n,_) ->
      let n' = Name.strip_lskip n in 
      [(Name.to_rope n', Name.to_rope_tex Term_var n', p.locn)]
  | P_constr(cd,ps) ->
      let n = (Ident.get_name cd.id_path) in
      let n' = Name.strip_lskip n in 
      [(Name.to_rope n', Name.to_rope_tex Term_ctor n', p.locn)]
  | P_record(s1,fields,s2) ->
      List.flatten (List.map (function (_,_,p) -> names_of_pat p) (Seplist.to_list fields))
  | P_tup(s1,ps,s2) ->
      List.flatten (List.map names_of_pat (Seplist.to_list ps))
  | P_list(s1,ps,s2) ->
      List.flatten (List.map names_of_pat (Seplist.to_list ps))
  | P_paren(s1,p,s2) ->
      names_of_pat p
  | P_cons(p1,s,p2) ->
      names_of_pat p1 @ names_of_pat p2
  | P_lit(l) ->
      []


and tex_of_output out = 
  match to_rope_option_tex T.lex_skip T.need_space true out with
  | None -> r""
  | Some r -> r


and tex_inc_letbind (lb, l) lhs_keyword = match lb with
  | Let_val(p,topt,s2,e) ->
      let (source_name, typeset_name) = 
        match names_of_pat p with 
        | [(source_name, typeset_name, l)] -> (source_name, typeset_name) 
(* ghastly temporary hacks *)
        | (source_name, typeset_name, l)::_ -> (source_name, typeset_name) 
        | [] -> (gensym_tex_command(),r"")
        (* SO: The next case causes an unused case warning *)
        (*| _ -> raise (Failure "tex_inc_letbind found <> 1 name")*) in
      let latex_name = Output.tex_command_name source_name in
      let latex_label = Output.tex_command_label source_name in
      let pre_comment = r"" (* PLACEHOLDER *) in      
      let post_comment = r"" (* PLACEHOLDER *) in      
      let lhs_output = 
        begin
          pat p ^ 
          match topt with
          | None -> emp 
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
        end ^
        ws s2 ^ T.def_binding in
      let rhs_output = exp e in

      let lhs = tex_of_output lhs_output in
      let rhs = tex_of_output rhs_output in
      make_lemdefn latex_name latex_label typeset_name pre_comment lhs_keyword lhs rhs post_comment


  | Let_fun(clause) ->
      let (function_name, ps, topt, pre_equal_comment, e) = clause in
      let source_name =  (function_name.term : Name.lskips_t) in
      let typeset_name = (Name.to_rope_tex Term_var (Name.strip_lskip source_name)) in
      let latex_name = Output.tex_command_name (Name.to_rope (Name.strip_lskip source_name)) in
      let latex_label = Output.tex_command_label (Name.to_rope (Name.strip_lskip source_name)) in
      let pre_comment = r"" (* PLACEHOLDER *) in      
      let post_comment = r"" (* PLACEHOLDER *) in      

      let lhs_output = 
        (Name.to_output Term_var source_name) ^ 
        begin
          match ps with
          | [] ->
              emp
          | _ ->
              texspace ^ 
              concat texspace (List.map pat ps) 
        end ^
        begin
          match topt with
          | None -> emp 
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
        end ^
        ws pre_equal_comment ^ T.def_binding in
      let rhs_output = exp e in
      let lhs = tex_of_output lhs_output in
      let rhs = tex_of_output rhs_output in
      make_lemdefn latex_name latex_label typeset_name pre_comment lhs_keyword lhs rhs post_comment


and def_tex_inc d : (Ulib.Text.t*Ulib.Text.t) list = match d with

(*   (\* A single type abbreviation *\) *)
(*   | Type_def(s1, l) when is_abbrev l-> *)
(*       begin *)
(*         match Seplist.hd l with *)
(*           | (s2,tvs,s3,(n,l),Te_abbrev(s4,t)) -> *)
(*               ws s1 ^ *)
(*               T.type_abbrev_start ^ *)
(*               tdef_tctor T.type_abbrev_name_quoted s2 tvs s3 n ^ *)
(*               tyexp_abbrev s4 t ^ *)
(*               T.type_abbrev_end *)
(*           | _ -> assert false *)
(*       end *)

(*   (\* A single record definition *\) *)
(*   | Type_def(s1, l) when is_rec l-> *)
(*       begin *)
(*         match Seplist.hd l with *)
(*           | (s2,tvs,s3,(n,l),Te_record(s4,s5,fields,s6)) -> *)
(*               ws s1 ^ *)
(*               T.typedefrec_start ^ *)
(*               tdef_tctor false s2 tvs s3 n ^ *)
(*               tyexp_rec s4 s5 fields s6 ^ *)
(*               T.typedefrec_end *)
(*           | _ -> assert false *)
(*       end *)

(*   | Type_def(s, defs) -> *)
(*       ws s ^ *)
(*       T.typedef_start ^ *)
(*       flat (Seplist.to_sep_list tdef (sep T.typedef_sep) defs) ^ *)
(*       T.typedef_end *)

  | Val_def(Let_def(s1, targets,bind),tvs) ->
      if in_target targets then
        let lhs_keyword = 
          tex_of_output (ws s1 ^ T.def_start) in
        [tex_inc_letbind (bind) lhs_keyword]
      else
        []


  | _ -> []

(*   | Module(s1,(n,l),s2,s3,ds,s4) ->  *)
(*       ws s1 ^ *)
(*       T.module_module ^ *)
(*       Name.to_output Module_name n ^ *)
(*       ws s2 ^ *)
(*       kwd "=" ^ *)
(*       ws s3 ^ *)
(*       T.module_struct ^ *)
(*       defs ds ^ *)
(*       ws s4 ^ *)
(*       T.module_end *)
(*   | Rename(s1,(n,l),s2,m) -> *)
(*       ws s1 ^ *)
(*       T.module_module ^ *)
(*       Name.to_output Module_name n ^ *)
(*       ws s2 ^ *)
(*       kwd "=" ^ *)
(*       Ident.to_output Module_name T.path_sep m.id_path *)
(*   | Open(s,m) -> *)
(*       ws s ^ *)
(*       T.module_open ^ *)
(*       Ident.to_output Module_name T.path_sep m.id_path *)
(*   | Indreln(s,targets,clauses) -> *)
(*       if in_target targets then *)
(*         ws s ^ *)
(*         T.reln_start ^ *)
(*         (if T.target = None then *)
(*            targets_opt targets  *)
(*          else *)
(*            emp) ^ *)
(*         flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^ *)
(*         T.reln_end *)
(*       else *)
(*         emp *)
(*   | Val_spec(s1,(n,l),s2,(constraint_pre,t)) -> *)
(*       ws s1 ^ *)
(*       kwd "val" ^ *)
(*       Name.to_output Term_var n ^ *)
(*       ws s2 ^ *)
(*       T.typ_sep ^ *)
(*       begin *)
(*         match constraint_pre with *)
(*           | None -> emp *)
(*           | Some(cp) -> constraint_prefix cp *)
(*       end ^ *)
(*       typ t *)
(*   | Subst(s1,s2,target,s3,n,args,s4,body) -> *)
(*       if (T.target = None) then *)
(*         ws s1 ^ *)
(*         kwd "sub" ^ *)
(*         ws s2 ^ *)
(*         kwd "[" ^ *)
(*         target_to_output Term_var target ^ *)
(*         ws s3 ^ *)
(*         kwd "]" ^ *)
(*         Name.to_output Term_var n.term ^ *)
(*         flat (List.map (fun n -> Name.to_output Term_var n.term) args) ^  *)
(*         ws s4 ^ *)
(*         kwd "=" ^ *)
(*         exp body *)
(*       else *)
(*         emp *)
(*   | Instance(s1,(cp,s2,id,t,s3),methods,s4) -> *)
(*       ws s1 ^ *)
(*       kwd "instance" ^ *)
(*       begin *)
(*         match cp with *)
(*           | None -> emp *)
(*           | Some(cp) -> constraint_prefix cp *)
(*       end ^ *)
(*       ws s2 ^ *)
(*       kwd "(" ^ *)
(*       Ident.to_output Term_method T.path_sep id ^ *)
(*       typ t ^ *)
(*       ws s3 ^ *)
(*       kwd ")" ^ *)
(*       flat (List.map (fun d -> def (Val_def(d))) methods) ^ *)
(*       ws s4 ^ *)
(*       kwd "end" *)
(*   | Class(s1,s2,(n,l), tv, s3, specs, s4) ->  *)
(*       ws s1 ^ *)
(*       kwd "class" ^ *)
(*       ws s2 ^ *)
(*       kwd "(" ^ *)
(*       Name.to_output Class_name n ^ *)
(*       tyvar tv ^ *)
(*       ws s3 ^ *)
(*       kwd ")" ^ *)
(*       flat (List.map  *)
(*               (fun (s1,(n,l),s2,t) -> *)
(*                 ws s1 ^ *)
(*                 kwd "val" ^ *)
(*                 Name.to_output Term_method n ^ *)
(*                 ws s2 ^ *)
(*                 kwd ":" ^ *)
(*                 typ t) *)
(*               specs) ^ *)
(*       ws s4 ^ *)
(*       kwd "end" *)


and html_source_name_letbind (lb,l) = match lb with
  | Let_val(p,topt,s2,e) ->
      (match names_of_pat p with 
      | [(source_name, typeset_name, l)] -> Some source_name
    (* ghastly temporary hacks *)
      | (source_name, typeset_name, l)::_ -> Some source_name
      | [] -> None)
  | Let_fun(clause) ->
      let (function_name, ps, topt, pre_equal_comment, e) = clause in
      let source_name =  (function_name.term : Name.lskips_t) in
      Some (Name.to_rope (Name.strip_lskip (source_name)))

and html_source_name_def d = match d with
  | Val_def(Let_def(s1, targets,bind),tvs) ->
      html_source_name_letbind bind
  | _ -> None

and html_link_def d = 
  match html_source_name_def d with
  | None -> emp
  | Some s -> 
      let sr = Ulib.Text.to_string s in
      kwd ( String.concat "" ["\n<a name=\"";sr;"\">"])


and defs (ds:def list) =
  List.fold_right
    (fun ((d,s),l) y -> 
       begin
         match T.target with 
         | Some (Ast.Target_isa _) -> isa_def d
         | Some (Ast.Target_tex _) -> raise (Failure "should be unreachable")
         | Some (Ast.Target_html _) -> html_link_def d ^ def d
         | _ -> def d
       end ^

       begin
         match s with
           | None ->
               emp
           | Some(s) -> 
               ws s ^ kwd ";;"
       end ^
       y)
    ds 
    emp

  
(* Sets in Isabelle: the standard set notation only supports {x. P x} to define
 * a set, but for example not {f x. P x}. 
 * We use the Isabelle notation { f x | x. P x } to cope with that restriction.
 * So the general case {exp1|exp2} has to be translated to {exp1|Vars(exp1).exp2} *)
(* TODO: try to move as much as possible to trans.ml and use normal def function *)

and isa_def d : Output.t = match d with 
  | Type_def(s1, l) when is_abbrev l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,Te_abbrev(s4,t)) ->
              ws s1 ^
              T.type_abbrev_start ^
              tdef_tctor (check_type_name n) tvs n ^
              tyexp_abbrev s4 t ^
              T.type_abbrev_end
          | _ -> assert false
      end
  
  | Type_def(s1, l) when is_rec l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,Te_record(s4,s5,fields,s6)) ->
              ws s1 ^
              T.typedefrec_start ^
              tdef_tctor (check_type_name n) tvs n ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end
          | _ -> assert false
      end

  | Val_def (Let_def(s1, targets,bind),tvs) ->
      if in_target targets then 
        ws s1 ^ T.def_start ^ 
        (if T.target = None then
           targets_opt targets 
         else
           emp) ^
        isa_letbind bind ^ T.def_end    
      else emp  
  
  | Val_def (Rec_def (s1, s2, targets, clauses),tvs) ->
      if in_target targets then 
        ws s1 ^ ws s2 ^ kwd "rec" ^ 
        (if T.target = None then
           targets_opt targets 
         else
           emp) ^
        flat (Seplist.to_sep_list (isa_funcl (kwd "= ")) (sep T.def_sep) clauses)
      else emp
      
  | Val_spec(s1,(n,l),s2,t) ->
      raise (Util.TODO(l, "Isabelle: Top-level type constraints omited; should not occur at the moment"))

  | Indreln(s,targets,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        (if T.target = None then
           targets_opt targets 
         else
           emp) ^
        (try 
          let (s1, qnames, s2, e, s3, rname, es) = List.hd (Seplist.to_list clauses) in 
          isa_mk_typed_def_header(Name.to_output Term_var rname.term,[], None,Typed_ast.annot_to_typ rname) 
        with 
          | Failure _ -> raise (Util.TODO(Ast.Unknown,"Isabelle: inductive relation without clauses?"))
        )^
        flat (Seplist.to_sep_list isa_indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp
        
  | _ -> def d


and check_type_name n = List.mem (Name.to_rope (Name.strip_lskip n)) Isa_keywords.keywords
  
  (*
        
  | Module(s1,n,s2,s3,defs,s4) ->
      raise (TODO "Isabelle Module Definition; should not occur at the moment")

  | Rename(s1,n,s2,m) ->
      raise (TODO "Isabelle Renames; should not occur at the moment")

  | Open(s,m) ->
      raise (TODO "Isabelle Opens; should not occur at the moment")

  | Include(s,m) -> 
      raise (TODO "Isabelle Includes; should not occur at the moment")


  | Subst(s1,s2,target,s3,n,args,s4,body) -> 
      raise (TODO "Isabelle substitution")    

*)

(*********************)

and (^^^^) = Ulib.Text.(^^^)

and to_rope_tex_def d : Ulib.Text.t = 
  match to_rope_option_tex T.lex_skip T.need_space true (def d) with
  | None -> r""
  | Some rr -> 
      r"\\lemdef{\n" ^^^^
      rr  ^^^^
      r"\n}\n"


let defs ((ds:def list),end_lex_skips) =
  match T.target with
  | Some (Ast.Target_tex _) -> 
      Ulib.Text.concat (r"") (List.map (function ((d,s),l) -> to_rope_tex_def d) ds) ^^^^
      (match to_rope_option_tex T.lex_skip T.need_space true (ws end_lex_skips) with None -> r"" | Some rr -> 
        r"\\lemdef{\n" ^^^^
        rr  ^^^^
        r"\n}\n"
      )(* TODO*)
  | _ ->
      to_rope T.string_quote T.lex_skip T.need_space (defs ds ^ ws end_lex_skips)


let rec batrope_pair_concat : (Ulib.Text.t * Ulib.Text.t) list -> (Ulib.Text.t * Ulib.Text.t)
  = function
    |  [] -> (r"",r"")
    |  (r1,r2)::rrs  -> let (r1',r2') = batrope_pair_concat rrs in (r1^^^^r1', r2^^^^r2') 

(* for -inc.tex file *)
let defs_inc ((ds:def list),end_lex_skips) =
  match T.target with
  | Some (Ast.Target_tex _) -> 
      batrope_pair_concat (List.map (function ((d,s),l) -> batrope_pair_concat (def_tex_inc d)) ds)
  | _ ->
      raise (Failure "defs_inc called on non-tex target")



let header_defs ((defs:def list),(end_lex_skips : Typed_ast.lskips)) =  
  to_rope T.string_quote T.lex_skip T.need_space
    (List.fold_right 
       (fun ((d,s),l) y ->
          begin match T.target with

              Some (Ast.Target_isa _) -> 
                begin 
                  match d with 
                      Open(s,m) -> 
                        kwd "\t \""^Ident.to_output Module_name T.path_sep m.id_path ^kwd "\""
                    | _ -> emp
                end

            | _ -> emp
          end ^ 
          y)
       defs 
       emp)

end

module Make(C : sig val avoid : var_avoid_f end) = struct
  module Dummy = struct let comment_def d = assert false end

  module C = struct let check = None let avoid = Some(C.avoid) end

  let ident_defs defs =
    let module B = F(Identity)(C)(Dummy) in
      B.defs defs

  let html_defs defs =
    let module B = F(Html)(C)(Dummy) in
      B.defs defs

  let tex_defs defs =
    let module B = F(Tex)(C)(Dummy) in
      B.defs defs

  let tex_inc_defs defs =
    let module B = F(Tex)(C)(Dummy) in
      B.defs_inc defs

  module Comment_def = struct
    let comment_def d = ident_defs ([d],None)
  end

  let hol_defs defs =
    let module B = F(Hol)(C)(Comment_def) in
      B.defs defs

  let ocaml_defs defs =
    let module B = F(Ocaml)(C)(Comment_def) in
      B.defs defs

  let isa_defs defs =
    let module B = F(Isa)(C)(Comment_def) in
      B.defs defs

  let isa_header_defs defs =
    let module B = F(Isa)(C)(Comment_def) in
      B.header_defs defs

  let coq_defs defs =
    let module B = F(Coq)(C)(Comment_def) in
      B.defs defs
end
