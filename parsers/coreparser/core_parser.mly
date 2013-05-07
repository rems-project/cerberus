%{
open Global

type expr =
  | Eskip
  | Econst of int
(*  | Eaddr of Core.mem_addr *)
  | Esym of string
  | Eop of Core.binop * expr * expr
  | Etrue
  | Efalse
  | Enot of expr
  | Ectype of Ail.ctype
  | Elet of string * expr * expr
  | Eif of expr * expr * expr
  | Eproc of string * expr list
  | Ecall of string * expr list
  | Esame of expr * expr
  | Eundef
  | Eerror
  | Eaction of paction
  | Eunseq of expr list
  | Ewseq of (string option) list * expr * expr
  | Esseq of (string option) list * expr * expr
  | Easeq of string option * action * paction
  | Eindet of expr (* TODO: add unique indices *)
  | Ebound of int * expr
  | Esave of string * expr
  | Erun of string
  | Eret of expr

and action =
  | Create of expr
  | Alloc of expr
  | Kill of expr
  | Store of expr * expr * expr
  | Load of expr * expr
and paction = Core.polarity * action


(* TODO *)
let convert e arg_syms fsyms =
  let rec f ((count, syms) as st) = function
    | Eskip                     -> Core.Eskip
    | Econst n                  -> Core.Econst n
    | Esym a                    -> Boot.print_debug ("LOOKING FOR> " ^ a) $ Core.Esym (Pmap.find a syms) (* Error handling *)
    | Eop (binop, e1, e2)       -> Core.Eop (binop, f st e1, f st e2)
    | Etrue                     -> Core.Etrue
    | Efalse                    -> Core.Efalse
    | Enot e                    -> Core.Enot (f st e)
    | Ectype ty                 -> Core.Ectype ty
    | Elet (a, e1, e2) ->
        let _a = (count, Some a) in
        Core.Elet (_a, f st e1, f (count+1, Pmap.add a _a syms) e2)

    | Eif (e1, e2, e3)          -> Core.Eif (f st e1, f st e2, f st e3)
    | Eproc (func, args)        -> Core.Eproc (Pset.empty compare, Pmap.find func fsyms, List.map (f st) args)
    | Ecall (func, args)        -> Core.Ecall (Pmap.find func fsyms, List.map (f st) args)
    | Esame (e1, e2)            -> Core.Esame (f st e1, f st e2)
    | Eundef                    -> Core.Eundef
    | Eerror                    -> Core.Eerror
    | Eaction pact              -> Core.Eaction (g st pact)
    | Eunseq es                 -> Core.Eunseq (List.map (f st) es)
    | Ewseq (_as, e1, e2) ->
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = (c, Some sym) in
                          Boot.print_debug ("ADDING> " ^ sym) (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        
        Core.Ewseq (List.rev _as', f st e1, f (count', syms') e2)



    | Esseq (_as, e1, e2)       -> let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
                                     match sym_opt with
                                       | Some sym -> let _a = (c, Some sym) in (c+1, Some _a :: _as, Pmap.add sym _a syms)
                                       | None     -> (c+1, None :: _as, syms)) (count, [], Pmap.empty compare) _as in
                                   
                                   Core.Esseq (List.rev _as', f st e1, f (count', syms') e2)
    | Easeq (_a_opt, act, pact) ->
(
        match _a_opt with
          | Some _a -> let _a' = (count, Some _a) in
                       print_endline ("ADDING> " ^ _a);
                       Core.Easeq (Some _a', snd (g st (Core.Pos, act)), g (count+1, Pmap.add _a _a' syms) pact)
          | None    -> Core.Easeq (None, snd (g st (Core.Pos, act)), g st pact)
            
)            
            

    | Eindet e                  -> Core.Eindet (f st e)
    | Ebound (i, e)             -> failwith "TODO: bound"
    | Esave (k, e)              -> failwith "TODO: save"
    | Erun k                    -> failwith "TODO: run"
    | Eret e -> Core.Eret (f st e)
  and g st (p, act) =(p,
    match act with
      | Create e_ty            -> (Pset.empty compare, Core.Create (f st e_ty, []))
      | Alloc e_n              -> (Pset.empty compare, Core.Alloc (f st e_n, []))
      | Kill e_o               -> (Pset.empty compare, Core.Kill (f st e_o))
      | Store (e_ty, e_o, e_n) -> (Pset.empty compare, Core.Store (f st e_ty, f st e_o, f st e_n))
      | Load (e_ty, e_o)       -> (Pset.empty compare, Core.Load (f st e_ty, f st e_o)))
  in f (0, arg_syms) e


let mk_file funs =
  let (main, _, fsyms, fun_map) =
    List.fold_left (fun (main, count, fsyms, fun_map) (fname, fdef) ->
      (* TODO: better error *)
      if Pmap.mem fname fsyms then failwith ("duplicate definition of `" ^ fname ^ "'")
      else
        let a_fun = (count, Some fname) in
        ((if fname = "main" then Some a_fun else main), count+1,
         Pmap.add fname a_fun fsyms,
         Pmap.add a_fun fdef fun_map)
    ) (None, 0, Pmap.empty compare, Pmap.empty compare) funs
  in
  let fun_map' =
    Pmap.map (fun (coreTy_ret, args, fbody) ->
      let (_, arg_syms, args') = List.fold_left (fun (i, m, args') (x, ty) ->
        let _a = (i, Some x) in (i+1, Pmap.add x _a m, (_a, ty) :: args'))
        (0, Pmap.empty compare, []) args in
      (coreTy_ret, args', convert fbody arg_syms fsyms)) fun_map in
  match main with
    | Some a_main -> Left { Core.main=    a_main;
                            Core.fun_map= fun_map' }
    | None        -> Right fun_map'



(* HACK for now (maybe we should just get back to concrete names for ctypes) *)
let ctypes_names = ref (0, Pmap.empty Pervasives.compare)

(*val subst: string -> Symbol.t *)
let subst name =
  let (z, ns) = !ctypes_names in
  if Pmap.mem name ns then
    Pmap.find name ns
  else
    let n = (z, Some name) in
    ctypes_names := (z+1, Pmap.add name n ns);
    n

%}

%token CREATE ALLOC KILL STORE LOAD
%token <int> INT_CONST
%token <string> SYM
%token SKIP RET
%token NOT
%token TRUE FALSE
%token LET IN
%token FUN PROC END
%token SAVE RUN
%token PLUS MINUS STAR SLASH PERCENT
%token EQ LT
%token SLASH_BACKSLASH BACKSLASH_SLASH
%token TILDE
%token EXCLAM
%token PIPE_PIPE SEMICOLON PIPE_GT GT_GT
%token UNDERSCORE
%token LT_MINUS
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET DOT COMMA COLON COLON_EQ
%token SAME
%token UNDEF ERROR
%token IF THEN ELSE
%token INTEGER BOOLEAN ADDRESS CTYPE UNIT


(* ctype tokens *)
%token CONST RESTRICT VOLATILE ATOMIC SHORT INT LONG
%token BOOL SIGNED UNSIGNED FLOAT DOUBLE COMPLEX CHAR VOID STRUCT UNION ENUM
%token SIZE_T INTPTR_T WCHAR_T CHAR16_T CHAR32_T


%token EOF

%left SLASH_BACKSLASH BACKSLASH_SLASH
%left ELSE
%left NOT
%left PLUS MINUS
%left STAR SLASH PERCENT
%left EQ LT

%start start
%type <(Global.zero Core.file, Global.zero Core.fun_map) Global.either> start

%%

n_ary_operator(separator, X):
  x1 = X separator x2 = X
    { [ x1; x2 ] }
| x = X; separator; xs = n_ary_operator(separator, X)
    { x :: xs }

delimited_nonempty_list(opening, separator, X, closing):
  x = X
   { [x] }
| xs = delimited(opening, n_ary_operator(separator, X),
  closing)
   { xs }

start:
| funs = nonempty_list(fun_declaration) EOF
    { mk_file funs }

core_base_type:
| INTEGER
    { Core.Integer }
| BOOLEAN
    { Core.Boolean }
| ADDRESS
    { Core.Address }
| CTYPE
    { Core.Ctype }
| UNIT
    { Core.Unit }

core_derived_type:
| baseTy = core_base_type
    { baseTy }
| baseTys = n_ary_operator(STAR, core_base_type)
    { Core.Tuple baseTys }

core_type:
| baseTy = core_derived_type
    { Core.TyBase baseTy }
| baseTy = delimited(LBRACKET, core_derived_type, RBRACKET)
    { Core.TyEffect baseTy }

(* BEGIN Ail types *)
qualifier:
| CONST
    { Ail.CONST }
| RESTRICT
    { Ail.RESTRICT }
| VOLATILE
    { Ail.VOLATILE }
(*
| ATOMIC
    { Ail.ATOMIC_Q }
*)

qualifiers:
| qs= list(qualifier)
    { Pset.from_list Pervasives.compare qs }

integer_base_type:
| CHAR
    { Ail.ICHAR }
| SHORT
    { Ail.SHORT }
| INT
    { Ail.INT }
| LONG
    { Ail.LONG }
| LONG LONG
    { Ail.LONG_LONG }
(*| EXTENDED_INTEGER of string *)

integer_type:
| BOOL
    { Ail.BOOL }
| SIGNED ibt= integer_base_type
    { Ail.SIGNED ibt }
| UNSIGNED ibt= integer_base_type
    { Ail.UNSIGNED ibt }

real_floating_type:
| FLOAT
    { Ail.FLOAT }
| DOUBLE
    { Ail.DOUBLE }
| LONG DOUBLE
    { Ail.LONG_DOUBLE }

basic_type:
| CHAR
    { Ail.CHAR }
| it= integer_type
    { Ail.INTEGER it }
| rft= real_floating_type
    { Ail.REAL_FLOATING rft }
| rft= real_floating_type COMPLEX
    { Ail.COMPLEX rft }

member_def:
| ty= ctype name= SYM 
    { (subst name, Ail.MEMBER ty) }
| ty= ctype name= SYM COLON n= INT_CONST
    { (subst name, Ail.BITFIELD (ty, n, None)) }

ctype:
| qs= qualifiers VOID
    { Ail.VOID qs }
| qs= qualifiers bty= basic_type
    { Ail.BASIC (qs, bty) }
| ty= ctype LBRACKET n_opt= INT_CONST? RBRACKET
    { Ail.ARRAY (ty, n_opt) }
| qs= qualifiers STRUCT tag= SYM mems= delimited(LBRACKET, separated_list(SEMICOLON, member_def), RBRACKET)
    { Ail.STRUCT (qs, subst tag, mems) }
| qs= qualifiers UNION tag= SYM mems= delimited(LBRACKET, separated_list(SEMICOLON, member_def), RBRACKET)
    { Ail.UNION (qs, subst tag, mems) }
| ENUM name= SYM
    { Ail.ENUM (subst name)}
| ty_ret= ctype tys= delimited(LPAREN, separated_list(COMMA, ctype), RPAREN)
    { Ail.FUNCTION (ty_ret, tys) }
| qs= qualifiers ty= ctype STAR
    { Ail.POINTER (qs, ty) }
| ATOMIC ty= ctype
    { Ail.ATOMIC ty }
| SIZE_T
    { Ail.SIZE_T }
| INTPTR_T
    { Ail.INTPTR_T }
| WCHAR_T
    { Ail.WCHAR_T }
| CHAR16_T
    { Ail.CHAR16_T }
| CHAR32_T
    { Ail.CHAR32_T }

(* END Ail types *)

%inline binary_operator:
| PLUS            { Core.OpAdd }
| MINUS           { Core.OpSub }
| STAR            { Core.OpMul }
| SLASH           { Core.OpDiv }
| PERCENT         { Core.OpMod }
| EQ              { Core.OpEq  }
| LT              { Core.OpLt  }
| SLASH_BACKSLASH { Core.OpAnd }
| BACKSLASH_SLASH { Core.OpOr  }

action:
| CREATE ty = delimited(LPAREN, expr, RPAREN)
    { Create ty }
| ALLOC n = expr
    { Alloc n }
| KILL e = expr
    { Kill e }
| STORE LPAREN ty = expr COMMA x = expr COMMA n = expr RPAREN
    { Store (ty, x, n) }
| LOAD LPAREN ty = expr COMMA x = expr RPAREN
    { Load (ty, x) }

paction:
| act = action
    { (Core.Pos, act) }
| TILDE act = action
    { (Core.Neg, act) }

pattern_elem:
| UNDERSCORE    { None   }
| LPAREN RPAREN { None   } (* TODO: add a new constructor in the Ast for better type/syntax checking *)
| a = SYM       { Some a }

pattern:
| _as = delimited_nonempty_list(LPAREN, COMMA, pattern_elem, RPAREN) { _as }

unseq_expr:
| es = delimited(LBRACKET, n_ary_operator(PIPE_PIPE, seq_expr), RBRACKET)
    { Eunseq es }

basic_expr:
| e = expr
    { e }
| p = paction
    { Eaction p }

extended_expr:
| e = basic_expr
    { e }
| e = unseq_expr
    { e }

seq_expr:
| e = basic_expr
    { e }
| _as = pattern LT_MINUS e1 = extended_expr SEMICOLON e2 = impure_expr
    { Esseq (_as, e1, e2) }
| e1 = extended_expr SEMICOLON e2 = impure_expr
    { Esseq ([], e1, e2) }
| _as = pattern LT_MINUS e1 = extended_expr GT_GT e2 = impure_expr
    { Ewseq (_as, e1, e2) }
| e1 = extended_expr GT_GT e2 = impure_expr
    { Ewseq ([], e1, e2) }
| _as = pattern LT_MINUS a = action PIPE_GT p = paction
    { match _as with
      | [alpha] -> Easeq (alpha, a, p)
      | _       -> assert false }
    (* TODO Really, we just want to parse a "SYM" an not a "pattern". *)
| SAVE d = SYM DOT e = impure_expr
    { Esave (d, e) }
| RUN d = SYM
    { Erun d }


impure_expr:
| e = seq_expr
    { e }
| e = unseq_expr
    { e }



expr:
| e = delimited(LPAREN, expr, RPAREN)
    { e }

| SKIP
    { Eskip }

| n = INT_CONST
    { Econst n }

| a = SYM
    { Esym a }

| e1 = expr op = binary_operator e2 = expr
    { Eop (op, e1, e2) }

| TRUE
    { Etrue }

| FALSE
    { Efalse }

| NOT e = expr
    { Enot e }

| ty = ctype
    { Ectype ty }

| LET a = SYM EQ e1 = expr IN e2 = impure_expr END (* TODO: END is tasteless. *)
    { Elet (a, e1, e2) }

| IF b = expr THEN e1 = impure_expr ELSE e2 = impure_expr (* TODO: may need to also allow unseq_expr *)
    { Eif (b, e1, e2) }

(* HACK: shouldn't be in the parser, but insted impure Ecall should be converted to Eproc by the typechecker *)
| f = SYM es = delimited(LBRACE, separated_list(COMMA, expr), RBRACE)
    { Eproc (f, es) }

| f = SYM es = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Ecall (f, es) }
(*
| SAME LPAREN e1 = expr e2 = expr RPAREN
    { Esame (e1, e2) }
*)
| UNDEF
    { Eundef }
| ERROR
    { Eerror }

| e = delimited(LBRACKET, seq_expr, RBRACKET) (* TODO: may need to also allow unseq_expr *)
    { Eindet e } (* TODO: the index *)


| RET e = expr
    { Eret e }


fun_argument:
| x = SYM COLON ty = core_base_type
    { (x, ty) }

fun_declaration:
| FUN fname = SYM args = delimited(LPAREN, separated_list(COMMA, fun_argument), RPAREN) COLON coreTy_ret = core_type COLON_EQ fbody = impure_expr
  { (fname, (coreTy_ret, List.rev args, fbody)) }

%%
