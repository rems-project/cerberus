/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */

%token <int> INT
%token <string> ID
%token TRUE FALSE
%token LPAREN RPAREN
%token PLUS MINUS TIMES DIV
%token LT GT LE GE EQ NE
%token MINIMUM MAXIMUM
%token MIN_U32 MIN_U64 MAX_U32 MAX_U64 MIN_I32 MIN_I64 MAX_I32 MAX_I64
%token EOF
%left LT GT LE GE EQ NE
%left PLUS MINUS
%left TIMES DIV
%left MAXIMUM MINIMUM
%start <IndexTerms.parse_ast> prog
%%

 
prog:
  | v = expr EOF { v }
;

expr:
  | TRUE                    { IndexTerms.Bool true }
  | FALSE                   { IndexTerms.Bool false }
  | MIN_U32                 { IndexTerms.min_u32 }
  | MIN_U64                 { IndexTerms.max_u64 }
  | MAX_U32                 { IndexTerms.max_u32 }
  | MAX_U64                 { IndexTerms.max_u64 }
  | MIN_I32                 { IndexTerms.min_i32 }
  | MIN_I64                 { IndexTerms.max_i64 }
  | MAX_I32                 { IndexTerms.max_i32 }
  | MAX_I64                 { IndexTerms.max_i64 }
  | i = INT                 { IndexTerms.Num (Z.of_int i) }
  | id = ID                 { IndexTerms.S id }
  | LPAREN expr RPAREN      { $2 }
  | expr LT expr            { IndexTerms.LT ($1,$3) }
  | expr GT expr            { IndexTerms.GT ($1,$3) }
  | expr LE expr            { IndexTerms.LE ($1,$3) }
  | expr GE expr            { IndexTerms.GE ($1,$3) }
  | expr EQ expr            { IndexTerms.EQ ($1,$3) }
  | expr NE expr            { IndexTerms.NE ($1,$3) }
  | expr PLUS expr          { IndexTerms.Add ($1,$3) }
  | expr MINUS expr         { IndexTerms.Sub ($1,$3) }
  | expr TIMES expr         { IndexTerms.Mul ($1,$3) }
  | expr DIV expr           { IndexTerms.Div ($1,$3) }
  | expr MINIMUM expr       { IndexTerms.Min ($1,$3) }
  | expr MAXIMUM expr       { IndexTerms.Max ($1,$3) }
;
