open CpPervasives

module P = Pprint
module A = CpAil

(* Import and define convenient infix operators. *)
open P.Operators

let pp_unop = function
  | A.MINUS -> P.minus
  | A.PLUS -> P.plus
  | A.ADDRESS -> P.ampersand
  | A.INDIRECTION -> P.star
  | A.BNOT -> P.tilde
  | A.POSTFIX_INCR -> P.plus ^^ P.plus
  | A.POSTFIX_DECR -> P.minus ^^ P.minus

let pp_arithop = function
  | Cabs.ADD -> P.plus
  | Cabs.SUB -> P.minus
  | Cabs.MUL -> P.star
  | Cabs.DIV -> P.slash
  | Cabs.MOD -> P.percent
  | Cabs.BAND -> P.ampersand
  | Cabs.BOR -> P.bar
  | Cabs.XOR -> P.caret
  | Cabs.SHL -> P.langle ^^ P.langle
  | Cabs.SHR -> P.rangle ^^ P.rangle

let pp_seqop = function
  | Cabs.AND -> P.ampersand ^^ P.ampersand
  | Cabs.OR -> P.bar ^^ P.bar
  | Cabs.COMMA -> P.comma

let pp_relop = function
  | Cabs.EQ -> P.equals ^^ P.equals
  | Cabs.NE -> P.bang ^^ P.equals
  | Cabs.LT -> P.langle
  | Cabs.GT -> P.rangle
  | Cabs.LE -> P.langle ^^ P.equals
  | Cabs.GE -> P.rangle ^^ P.equals

let pp_binop = function
  | Cabs.ARITHMETIC o -> pp_arithop o
  | Cabs.SEQUENTIAL o -> pp_seqop o
  | Cabs.RELATIONAL o -> pp_relop o

let showParens = P.parens

let pp_qualifier = function
  | Cabs.CONST -> !^ "const"

let pp_int_base_type = function
  | A.ICHAR -> !^ "char"
  | A.SHORT -> !^ "short"
  | A.INT -> !^ "int"
  | A.LONG -> !^ "long"
  | A.LONG_LONG -> !^ "long" ^^^ !^ "long"

let pp_int_type = function
  | A.BOOL -> !^ "_Bool"
  | A.UNSIGNED ib -> !^ "unsigned" ^^^ pp_int_base_type ib
  | A.SIGNED ib -> !^ "signed" ^^^ pp_int_base_type ib

let pp_basic_type = function
  | A.VOID -> !^ "void"
  | A.CHAR -> !^ "char"
  | A.INTEGER i -> pp_int_type i

let pp_suffix s =
  let to_string = function
    | Cabs.SUFFIX_UNSIGNED -> "U"
    | Cabs.SUFFIX_UNSIGNED_LONG -> "UL"
    | Cabs.SUFFIX_UNSIGNED_LONG_LONG -> "ULL"
    | Cabs.SUFFIX_LONG -> "L"
    | Cabs.SUFFIX_LONG_LONG -> "LL" in
  P.optional (P.text -| to_string) s

let pp_int_const (i, s) = !^ (BatBig_int.to_string i) ^^ pp_suffix s

let rec pp_type t =
  let f = pp_type in
  let pp_qs qs =
    let ins_space ds d = ds ^^ d ^^ P.space in
    P.fold ins_space (List.map pp_qualifier (BatSet.elements qs)) in
  match t with
  | A.BASE (qs, b) -> pp_qs qs ^^ pp_basic_type b
  | A.ARRAY (t, s) -> P.parens (f t) ^^^ P.brackets (!^ (BatInt.to_string s))
  | A.POINTER (qs, t) -> pp_qs qs ^^ P.parens (f t) ^^^ P.star
  | A.FUNCTION (t, ts) -> f t ^^^ P.parens (P.comma_list f ts)

let pp_type_class = function
  | A.Exp    t -> P.brackets (pp_type t) ^^ !^ "exp"
  | A.Lvalue t -> P.brackets (pp_type t) ^^ !^ "lvalue"

let pp_return_type = function
  | A.FUNCTION (t, _) -> pp_type t
  | _ -> raise_error "Not a function type!"

let pp_id id = !^ (CpSymbol.to_string_pretty id)

let rec pp_exp (d, exp) =
  let f = P.group -| P.parens -| pp_exp in
  match exp with
  | A.VARIABLE id -> pp_id id
  | A.UNARY (A.POSTFIX_INCR as o, e)
  | A.UNARY (A.POSTFIX_DECR as o, e) -> f e ^^ pp_unop o
  | A.UNARY (o, e) -> pp_unop o ^^ f e
  | A.BINARY ((Cabs.SEQUENTIAL Cabs.COMMA) as o, e1, e2) ->
      (f e1) ^^ (pp_binop o) ^^ P.space ^^ (f e2)
  | A.BINARY (o, e1, e2) -> (f e1) ^^^ (pp_binop o) ^^^ (f e2)
  | A.CALL (e, es) -> f e ^^ P.parens (P.comma_list f es)
  | A.ASSIGN (o_opt, e1, e2) ->
      (f e1) ^^^ (P.optional pp_arithop o_opt ^^ P.equals) ^^^ (f e2)
  | A.QUESTION (e1, e2, e3) ->
      P.group (f e1 ^^^ P.qmark ^/^ f e2 ^^^ P.colon ^/^ f e3)
  | A.CAST (t, e) -> P.parens (pp_type t) ^^^ f e
  | A.CONSTANT (Cabs.CONST_INT ic) -> pp_int_const ic
  | A.SIZEOF  t -> !^ "sizeof"  ^^ P.parens (pp_type t)
  | A.ALIGNOF t -> !^ "alignof" ^^ P.parens (pp_type t)

let pp_decl file id =
  let (t, st) = BatMap.find id file.A.id_map in
  pp_type t ^^^ pp_id id

let rec pp_stmt file (d, stmt) =
  let f_e = pp_exp in
  let f_s = pp_stmt file in
  match stmt with
  | A.SKIP -> P.semi
  | A.EXPRESSION e -> f_e e ^^ P.semi
  | A.BLOCK (_, ss) ->
      let block = P.sepmap P.break1 f_s ss in
      P.lbrace ^^ P.nest 2 (P.break1 ^^ block) ^/^ P.rbrace
  | A.IF (e, s1, s2) ->
      !^ "if" ^^^ P.parens (f_e e) ^^^ f_s s1 ^^^ !^ "else" ^^^ f_s s2
  | A.WHILE (e, s) ->
      !^ "while" ^^^ P.parens (f_e e) ^/^ f_s s
  | A.DO (e, s) ->
      !^ "do" ^/^ f_s s ^/^ !^ "while" ^^^ P.parens (f_e e)
  | A.BREAK -> !^ "break" ^^ P.semi
  | A.CONTINUE -> !^ "continue" ^^ P.semi
  | A.RETURN_VOID -> !^ "return" ^^ P.semi
  | A.RETURN_EXPRESSION e -> !^ "return" ^^^ f_e e ^^ P.semi
  | A.SWITCH (e, s) -> !^ "switch" ^^^ P.parens (f_e e) ^/^ f_s s
  | A.CASE (ic, s) -> pp_int_const ic ^^ P.colon ^^^ f_s s
  | A.DEFAULT s -> !^ "default" ^^ P.colon ^^^ f_s s
  | A.GOTO id -> !^ "goto" ^^^ pp_id id ^^ P.semi
  | A.LABEL (id, s) -> pp_id id ^^ P.colon ^^^ f_s s
  | A.DECLARATION ds ->
      let f_d (id, e) =
        let (t, st) = BatMap.find id file.A.id_map in
        pp_type t ^^^ pp_id id ^^^ P.equals ^^^ f_e e in
      P.comma_list f_d ds ^^ P.semi

let pp_function file (id, (args, s)) =
  let (t, st) = BatMap.find id file.A.id_map in
  pp_return_type t
  ^^^ pp_id id
  ^^^ P.parens (P.comma_list (pp_decl file) args)
  ^^^ (pp_stmt file s)

let pp_file ({A.function_map; _} as file) =
  let pp d f = d ^^ pp_function file f ^^ P.break1 in
  List.fold_left pp P.empty (BatMap.bindings function_map)

let pp_result pp = function
  | A.Program file -> pp file
  | A.Undefined -> !^ "Undefined" ^^ P.break1
  | A.Invalid   -> !^ "Invalid"   ^^ P.break1

let pp file = pp_result pp_file file
