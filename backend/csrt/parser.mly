/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */
/* https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param */
/* stealing some things from the core parser */


%parameter <Arg:Parse_ast.ParserArg>


%type <Parse_ast.parsed_condition> condition_entry
%start condition_entry



%{

  open Parse_ast
  open Locations
  open IndexTerms
  open Tokens

  let pit (start_p, end_p) pit_ = IndexTerm (region (start_p, end_p) None, pit_)

%}


%%





condition_entry:
  | v = condition EOF { v }
;


name: 
  | id = ID                 { id } 

obj: 
  | STAR o = obj                    { Pointee o }
  | o = obj DOTDOT id = name        { PredicateArg (o,id) }
  | id = name AT label = name       { Id (label,id) }
  | id = name                       { Id (Arg.default_label,id) }

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
  | UNOWNED LPAREN o = obj RPAREN         { Ownership (o, OUnowned) }
  | BLOCK LPAREN o = obj RPAREN           { Ownership (o, OBlock) }
  | e = expr                              { Constraint e }



