/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */

/* stealing some things from the core parser */

%{
open Parse_ast
open Locations

let pit (start_p, end_p) pit_ = IndexTerm (region (start_p, end_p) None, pit_)
%}

%token <int> INT
%token <string> ID
/* %token AT */
%token DOT DOTDOT /* COLON */
%token AMPERSAND STAR
%token TRUE FALSE
%token LPAREN RPAREN
%token PLUS MINUS DIV
%token LT GT LE GE EQ NE EQEQ
%token MINIMUM MAXIMUM
%token MIN_U32 MIN_U64 MAX_U32 MAX_U64 MIN_I32 MIN_I64 MAX_I32 MAX_I64
%token UNINIT UNOWNED
%token EOF
%left LT GT LE GE EQEQ NE
%left PLUS MINUS
%left DIV
%left MAXIMUM MINIMUM
%left STAR
%left DOT DOTDOT
%type <string Parse_ast.condition> condition_entry
%type <string Parse_ast.definition> definition_entry
%start condition_entry definition_entry
%%

 
condition_entry:
  | v = condition EOF { v }
;

definition_entry:
  | v = definition EOF { v }
;




name: 
  /* | label = ID AT id = ID   { (Some label,id) } */
  | id = ID                 { id } 

obj_: 
  | STAR o = obj_              { Pointee o }
  | o = obj_ DOTDOT id = name  { PredicateArg (o,id) }
  | o = obj_ DOT id = name     { StructMember (o,id) }
  | id = name                  { Id id }

obj:
  | AMPERSAND id = name       { VariableLocation id }
  | o = obj_                  { Obj_ o }

expr:
  | TRUE                    { pit ($startpos, $endpos) (Bool true) }
  | FALSE                   { pit ($startpos, $endpos) (Bool false) }
  | o = obj                 { pit ($startpos, $endpos) (Object o) }
  | MIN_U32                 { pit ($startpos, $endpos) MIN_U32 }
  | MIN_U64                 { pit ($startpos, $endpos) MIN_U64 }
  | MAX_U32                 { pit ($startpos, $endpos) MAX_U32 }
  | MAX_U64                 { pit ($startpos, $endpos) MAX_U64 }
  | MIN_I32                 { pit ($startpos, $endpos) MIN_I32 }
  | MIN_I64                 { pit ($startpos, $endpos) MIN_I64 }
  | MAX_I32                 { pit ($startpos, $endpos) MAX_I32 }
  | MAX_I64                 { pit ($startpos, $endpos) MAX_I64 }
  | i = INT                 { pit ($startpos, $endpos) (Num (Z.of_int i)) }
  | LPAREN expr RPAREN      { $2 }
  | expr LT expr            { pit ($startpos, $endpos) (LT ($1,$3)) }
  | expr GT expr            { pit ($startpos, $endpos) (GT ($1,$3)) }
  | expr LE expr            { pit ($startpos, $endpos) (LE ($1,$3)) }
  | expr GE expr            { pit ($startpos, $endpos) (GE ($1,$3)) }
  | expr EQEQ expr          { pit ($startpos, $endpos) (EQ ($1,$3)) }
  | expr NE expr            { pit ($startpos, $endpos) (NE ($1,$3)) }
  | expr PLUS expr          { pit ($startpos, $endpos) (Add ($1,$3)) }
  | expr MINUS expr         { pit ($startpos, $endpos) (Sub ($1,$3)) }
  | expr STAR expr          { pit ($startpos, $endpos) (Mul ($1,$3)) }
  | expr DIV expr           { pit ($startpos, $endpos) (Div ($1,$3)) }
  | expr MINIMUM expr       { pit ($startpos, $endpos) (Min ($1,$3)) }
  | expr MAXIMUM expr       { pit ($startpos, $endpos) (Max ($1,$3)) }
;



condition: 
  | UNOWNED o = obj_        { Ownership (o, Unowned) }
  | UNINIT o = obj_         { Ownership (o, Uninit) }
  | e = expr                { Constraint e }

definition: 
  | id = name EQ o = obj    { Definition (id,o) }

