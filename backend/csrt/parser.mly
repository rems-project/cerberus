/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */
/* https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param */
/* and from the c and core parsers */


%parameter <Arg:Parse_ast.ParserArg>


%type <Parse_ast.parsed_condition> condition_entry
%start condition_entry



%{

  open Parse_ast
  open Locations
  open IndexTerms
  open Tokens
  open Cerb_frontend.Ctype

  let pit (start_p, end_p) pit_ = IndexTerm (region (start_p, end_p) None, pit_)

%}


%%





condition_entry:
  | v = condition EOF { v }
;


name: 
  | id = ID                 { id } 

path: 
  | STAR p = path                    { Path.pointee p }
  | p = path DOTDOT id = name        { Path.predicateArg p id }
  | id = name AT label = name        { {label; name = id; path = []} }
  | id = name                        { {label = Arg.default_label; name = id; path = []} }

/* fix these to do the right thing */
integer_base_type:
  | SHORT INT?              { Short }
  | INT                     { Int_ }
  | LONG INT?               { Long }
  | LONG LONG INT?          { LongLong }

integer_type:
  | SIGNED CHAR             { Signed Ichar }
  | CHAR                    { Char }
  | SIGNED ibt = integer_base_type { Signed ibt }
  | UNSIGNED ibt = integer_base_type { Unsigned ibt }
  | ibt = integer_base_type { Signed ibt }


expr:
  | TRUE                    { pit ($startpos, $endpos) (Bool true) }
  | FALSE                   { pit ($startpos, $endpos) (Bool false) }
  | p = path                { pit ($startpos, $endpos) (Path p) }
  | MIN LPAREN it = integer_type RPAREN  { pit ($startpos, $endpos) (MinInteger it) }
  | MAX LPAREN it = integer_type RPAREN  { pit ($startpos, $endpos) (MaxInteger it) }
  | i = NUM                 { pit ($startpos, $endpos) (Num (Z.of_int i)) }
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
  | MIN LPAREN i1 = expr COMMA i2 = expr RPAREN    { pit ($startpos, $endpos) (Min (i1,i2)) }
  | MAX LPAREN i1 = expr COMMA i2 = expr RPAREN    { pit ($startpos, $endpos) (Max (i1,i2)) }
;



condition: 
  | UNOWNED LPAREN p = path RPAREN        { Ownership (p, OUnowned) }
  | BLOCK LPAREN p = path RPAREN          { Ownership (p, OBlock) }
  | e = expr                              { Constraint e }



