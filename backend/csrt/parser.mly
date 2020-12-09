/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */
/* https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param */
/* and from the c and core parsers */


/* todo: fix locations */

%parameter <Arg:Parse_ast.ParserArg>


%type <Parse_ast.parsed_spec> spec_entry
%start spec_entry



%{

  open Parse_ast
  open Locations
  open IndexTerms
  open Tokens
  open Cerb_frontend.Ctype
  open Pred

  let pit (start_p, end_p) pit_ = IndexTerm (region (start_p, end_p) None, pit_)

%}


%%





spec_entry:
  | o = ownership EOF                   { Ownership o }
  | e = expr EOF                        { Constraint e }


;



pred: 
  | UNOWNED                          { Unowned } 
  | BLOCK                            { Block } 
  | id = PID                         { Pred (Id.parse Location_ocaml.unknown id) } 

basename:
  | id = ID AT label = ID            { {label; v = id} }
  | id = ID                          { {label = Arg.default_label; v = id} }

access:
  | STAR a = access                 { Ownership.pointee_access a }
  | bn = basename                   { Ownership.{ name = bn; derefs = [] } }

%inline ownership:
  | p = pred LPAREN a = access RPAREN   { Ownership.{ access = a; pred = p } }


path: 
  | STAR p = path                      { Object.Path.Pointee p }
  | bn = basename                      { Object.Path.Var bn }


addr_or_path:
  | AMPERSAND bn = basename            { Object.AddrOrPath.Addr bn }
  | p = path                           { Object.AddrOrPath.Path p }

obj: 
  | LPAREN pr = pred LPAREN aop = addr_or_path RPAREN RPAREN DOT id = ID   { Object.Obj (aop, Some {pred = pr; arg = id}) }
  | aop = addr_or_path                                        { Object.Obj (aop, None) }
  


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

expr_or_obj:
  | o = obj                 { pit ($startpos, $endpos) (Object o) }
  | e = expr                { e }

expr:
  | TRUE                                    { pit ($startpos, $endpos) (Bool true) }
  | FALSE                                   { pit ($startpos, $endpos) (Bool false) }
  | i = NUM                                 { pit ($startpos, $endpos) (Num (Z.of_int i)) }
  | MIN LPAREN it = integer_type RPAREN     { pit ($startpos, $endpos) (MinInteger it) }
  | MAX LPAREN it = integer_type RPAREN     { pit ($startpos, $endpos) (MaxInteger it) }
  | POINTER_TO_INTEGER expr_or_obj        { pit ($startpos, $endpos) (PointerToIntegerCast ($2)) }
  | INTEGER_TO_POINTER expr_or_obj        { pit ($startpos, $endpos) (IntegerToPointerCast ($2)) }
  | expr_or_obj LT expr_or_obj            { pit ($startpos, $endpos) (LT ($1,$3)) }
  | expr_or_obj GT expr_or_obj            { pit ($startpos, $endpos) (GT ($1,$3)) }
  | expr_or_obj LE expr_or_obj            { pit ($startpos, $endpos) (LE ($1,$3)) }
  | expr_or_obj GE expr_or_obj            { pit ($startpos, $endpos) (GE ($1,$3)) }
  | expr_or_obj EQEQ expr_or_obj          { pit ($startpos, $endpos) (EQ ($1,$3)) }
  | expr_or_obj NE expr_or_obj            { pit ($startpos, $endpos) (NE ($1,$3)) }
  | expr_or_obj PLUS expr_or_obj          { pit ($startpos, $endpos) (Add ($1,$3)) }
  | expr_or_obj MINUS expr_or_obj         { pit ($startpos, $endpos) (Sub ($1,$3)) }
  | expr_or_obj STAR expr_or_obj          { pit ($startpos, $endpos) (Mul ($1,$3)) }
  | expr_or_obj DIV expr_or_obj           { pit ($startpos, $endpos) (Div ($1,$3)) }
  | MIN LPAREN i1 = expr_or_obj COMMA i2 = expr_or_obj RPAREN    { pit ($startpos, $endpos) (Min (i1,i2)) }
  | MAX LPAREN i1 = expr_or_obj COMMA i2 = expr_or_obj RPAREN    { pit ($startpos, $endpos) (Max (i1,i2)) }
  | LPAREN expr RPAREN { $2 }
;


