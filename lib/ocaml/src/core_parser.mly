%{
 open Core

 let syms = ref Pmap.empty


%}

%token CREATE ALLOC KILL STORE LOAD

%token <int> CONST
  
%token <string> SYM
%token <string> FNAME

%token SKIP

%token NOT

%token TRUE FALSE

%token LET IN

%token FUN END

%token PLUS MINUS STAR SLASH PERCENT
%token EQ LT
%token SLASH_BACKSLASH BACKSLASH_SLASH

%token TILDE

%token EXCLAM

%token PIPE_PIPE SEMICOLON PIPE_GT GT_GT

%token LPAREN_RPAREN UNDERSCORE
  
%token LT_MINUS

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA COLON COLON_EQ

%token SAME

%token UNDEF ERROR

%token IF THEN ELSE

%token INTEGER BOOLEAN ADDRESS CTYPE UNIT

(* TODO: hack *)
%token SIGNED INT


%start start
%type <(sym * (core_type * (sym * core_base_type) list * unit expr)) list> start

%%


start:
| funs = nonempty_list(fun_declaration)
    { funs }

core_base_type:
| INTEGER
    { integer }
| BOOLEAN
    { boolean }
| ADDRESS
    { address }
| CTYPE
    { ctype }
| UNIT
    { unit }
| baseTys = delimited (LPAREN, separated_nonempty_list(COMMA, core_base_type) , RPAREN)
    { baseTys }


core_type:
| baseTy = core_base_type
    { TyBase baseTy }
| baseTy = delimited(LBRACKET, core_base_type, RBRACKET)
    { TyEffect baseTy }

(* TODO: find how to use the defs in cparser.mly *)
type_name:
| SIGNED INT
    { Ail.BASIC (Pset.empty Pervasives.compare, (Ail.INTEGER (Ail.SIGNED Ail.INT))) }




binary_operator:
| PLUS            { OpAdd }
| MINUS           { OpSub }
| STAR            { OpMul }
| SLASH           { OpDiv }
| PERCENT         { OpMod }
| EQ              { OpEq  }
| LT              { OpLt  }
| SLASH_BACKSLASH { OpAnd }
| BACKSLASH_SLASH { OpOr  }




action:
| CREATE ty = delimited(LBRACE, expression, RBRACE)
    { Kcreate ty }
| ALLOC n = expression
    { Kalloc n }
| KILL a = SYM
    { Kkill a }
| STORE ty = delimited(LBRACE, expression, RBRACE) x = expression n = expression
    { Kstore (ty, x, n) }
| LOAD ty = delimited(LBRACE, expression, RBRACE) x = expression
    { Kload (ty, x) }
;

paction:
| act = action
    { Kaction (Pos, act) }
| TILDE act = action
    { Kaction (Neg, act) }
;

pattern_elem:
| UNDERSCORE    { None   }
| LPAREN_RPAREN { None   } (* TODO: add a new constructor in the Ast for better type/syntax checking *)
| a = SYM       { Some a }
;

pattern:
| UNDERSCORE { [None] }
| _as = delimited(LPAREN, separated_nonempty_list(COMMA, pattern_elem), RPAREN) { _as }
;

expression:
| SKIP
    { Kskip }

| n = CONST
    { Kconst n }

| a = SYM
    { Ksym a }

| e1 = expression op = binary_operator e2 = expression
    { Kop (op, e1, e2) }

| TRUE
    { Ktrue }

| FALSE
    { Kfalse }

| NOT e = expression
    { Knot e }

| ty = type_name
    { Kctype ty }

| LET a = SYM EQ e1 = expression IN e2 = expression
    { Klet (a, e1, e2) }

| IF b = expression THEN e1 = expression ELSE e2 = expression
    { Kif (b, e1, e2) }

| f = SYM es = delimited(LBRACE, separated_list(COMMA, expression), RBRACE)
    { Kcall (f, es) }

| SAME e1 = expression e2 = expression
    { Ksame (e1, e2) }

| UNDEF
    { Kundef }
| ERROR
    { Kerror }

| p = paction
    { Kaction p }

| es = separated_nonempty_list(PIPE_PIPE, expression)
    { Kunseq es }

| e1 = expression GT_GT e2 = expression
    { Kwseq ([], e1, e2) }

| _as = pattern LT_MINUS e1 = expression GT_GT e2 = expression
    { Kwseq (_as, e1, e2) }

| e1 = expression SEMICOLON e2 = expression
    { Ksseq ([], e1, e2) }

| _as = pattern GT_GT e1 = expression SEMICOLON e2 = expression
    { Ksseq (_as, e1, e2) }

| a = action PIPE_GT p = paction
    { Kaseq (None, a, p) }

| alpha = SYM LT_MINUS a = action PIPE_GT p = paction
    { Kaseq (Just alpha, a, p) }

| e1 = expression SEMICOLON e2 = expression
    { Ksseq ([], e1, e2) }

| _as = pattern LT_MINUS e1 = expression SEMICOLON e2 = expression
    { Ksseq (_as, e1, e2) }

| e = delimited(LBRACKET, expression, RBRACKET)
    { Kindet e } (* TODO: the index *)

| e = delimited(LPAREN, expression, RPAREN)
    { e }



fun_argument:
| x = SYM COLON ty = core_base_type
    { (x, ty) }

fun_declaration:
| FUN fname = FNAME args = delimited(LPAREN, separated_list(COMMA, fun_argument), RPAREN) COLON coreTy_ret = core_type COLON_EQ fbody = expression END
  { (fname, (coreTy_ret, args, fbody)) }

%%
