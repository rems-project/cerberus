%{


type expr =
  | Kskip
  | Kconst of int
(*  | Kaddr of Core.mem_addr *)
  | Ksym of string
  | Kop of Core.binop * expr * expr
  | Ktrue
  | Kfalse
  | Knot of expr
  | Kctype of Ail.ctype
  | Klet of string * expr * expr
  | Kif of expr * expr * expr
  | Kcall of string * expr list
  | Ksame of expr * expr
  | Kundef
  | Kerror
  | Kaction of paction
  | Kunseq of expr list
  | Kwseq of (string option) list * expr * expr
  | Ksseq of (string option) list * expr * expr
  | Kaseq of string option * action * paction
  | Kindet of expr (* TODO: add unique indices *)
  | Kbound of int * expr
  | Ksave of string * expr
  | Krun of string

and action =
  | Kcreate of expr
  | Kalloc of expr
  | Kkill of expr
  | Kstore of expr * expr * expr
  | Kload of expr * expr
and paction = Core.polarity * action


(* TODO *)
let convert e = Core.Kskip





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


%right GT_GT SEMICOLON
%nonassoc PIPE_PIPE


%start start
%type <(string * (Core.core_type * (string * Core.core_base_type) list * unit Core.expr)) list> start

%%


start:
| funs = nonempty_list(fun_declaration)
    { funs }

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
| baseTys = delimited (LPAREN, separated_nonempty_list(COMMA, core_base_type) , RPAREN)
    { Core.Tuple baseTys }


core_type:
| baseTy = core_base_type
    { Core.TyBase baseTy }
| baseTy = delimited(LBRACKET, core_base_type, RBRACKET)
    { Core.TyEffect baseTy }

(* TODO: find how to use the defs in cparser.mly *)
type_name:
| SIGNED INT
    { Ail.BASIC (Pset.empty Pervasives.compare, (Ail.INTEGER (Ail.SIGNED Ail.INT))) }




binary_operator:
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
| CREATE ty = delimited(LBRACE, expression, RBRACE)
    { Kcreate ty }
| ALLOC n = expression
    { Kalloc n }
| KILL e = expression
    { Kkill e }
| STORE ty = delimited(LBRACE, expression, RBRACE) x = expression n = expression
    { Kstore (ty, x, n) }
| LOAD ty = delimited(LBRACE, expression, RBRACE) x = expression
    { Kload (ty, x) }
;

paction:
| act = action
    { (Core.Pos, act) }
| TILDE act = action
    { (Core.Neg, act) }
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


bexpression:
| e = expression
    { ([], e) }
| _as = pattern LT_MINUS e = expression
    { (_as, e) }

expression:
| LPAREN e = expression RPAREN
    { e }

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

| LPAREN es = separated_nonempty_list(PIPE_PIPE, expression) RPAREN (* TODO: maybe temporary --> to get an ambigious grammar *)
    { Kunseq es }

(*
| e1 = expression GT_GT e2 = expression
    { Kwseq ([], e1, e2) }

| _as = pattern LT_MINUS e1 = expression GT_GT e2 = expression
    { Kwseq (_as, e1, e2) }
*)

| _as_e1 = bexpression GT_GT e2 = expression
    { let (_as, e1) = _as_e1 in Kwseq (_as, e1, e2) }

(*
| e1 = expression SEMICOLON e2 = expression
    { Ksseq ([], e1, e2) }

| _as = pattern GT_GT e1 = expression SEMICOLON e2 = expression
    { Ksseq (_as, e1, e2) }
*)

| _as_e1 = bexpression SEMICOLON e2 = expression
    { let (_as, e1) = _as_e1 in Ksseq (_as, e1, e2) }


| a = action PIPE_GT p = paction
    { Kaseq (None, a, p) }

| alpha = SYM LT_MINUS a = action PIPE_GT p = paction
    { Kaseq (Some alpha, a, p) }

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
  { (fname, (coreTy_ret, args, convert fbody)) }

%%
