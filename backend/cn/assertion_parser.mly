%{
(* adapting from core_parser.mly *)
open Assertion_parser_util
%}


%token <Z.t> Z
%token <string> NAME
%token <string> MEMBER

%token DOTDOT

%token PLUS
%token MINUS
%token STAR
%token SLASH
%token POWER

%token EQ
%token NE
%token LT
%token GT
%token LE
%token GE

%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA

%token QUESTION
%token COLON
%token OR
%token AND

%token NULL
%token POINTERCAST
%token INTEGERCAST

%token AMPERSAND
%token AT

%token EOF

/* %left EQ NE GT LT GE LE */
%left PLUS MINUS
%left STAR SLASH
/* %nonassoc POWER */
/* %nonassoc POINTERCAST */
%nonassoc MEMBER /* PREDARG */

%type <Ast.term>term
%type <Ast.condition>cond
%type <Ast.condition>start
%type <Z.t>integer

%start start integer

%%


start:
  | cond=cond EOF
      { cond }




%inline pred_with_args:
  | id=NAME args=delimited(LPAREN, separated_list(COMMA, term), RPAREN)
      { (id, args) }


integer:
  | MINUS z=Z
      { Z.minus_big_int z }
  | z=Z
      { z }
  | LPAREN z=integer RPAREN
      { z }


atomic_term:
  | LPAREN t= term RPAREN
      { t }
  | z=Z
      { Ast.Integer z }
  | a1=atomic_term member=MEMBER
/* taking the location-handling aspect from c_parser.mly */
      { Ast.Member (a1, Id.parse (Location_ocaml.region ($startpos, $endpos) (Some $startpos(member))) member) }
  | pred=NAME DOTDOT oarg=NAME
    { Ast. PredOutput (pred, oarg) }
  | AMPERSAND id=NAME
      { Ast.Addr id }
  | v=NAME
      { Ast.Var v }
  | STAR p=atomic_term
      { Ast.Pointee p }
  | NULL
      { Ast.Null }
  | LPAREN a=term RPAREN AT l=NAME
      { Ast.Env (a, l) }

arith_term:
  | a1=arith_or_atomic_term PLUS a2=arith_or_atomic_term
      { Ast.Addition (a1, a2) }
  | a1=arith_or_atomic_term MINUS a2=arith_or_atomic_term
      { Ast.Subtraction (a1, a2) } 
  | a1=arith_or_atomic_term STAR a2=arith_or_atomic_term
      { Ast.Multiplication (a1, a2) }
  | a1=arith_or_atomic_term SLASH a2=arith_or_atomic_term
      { Ast.Division (a1, a2) }
  | POWER LPAREN a1=term COMMA a2=term RPAREN
      { Ast.Exponentiation (a1, a2) }

arith_or_atomic_term:
  | a=arith_term
      { a }
  | a=atomic_term
      { a }

term:
  | t=arith_or_atomic_term
      { t }
  | a1=arith_or_atomic_term EQ a2=arith_or_atomic_term
      { Ast.Equality (a1, a2) }
  | a1=arith_or_atomic_term NE a2=arith_or_atomic_term
      { Ast.Inequality (a1, a2) }
  | a1=arith_or_atomic_term LT a2=arith_or_atomic_term
      { Ast.LessThan (a1, a2) }
  | a1=arith_or_atomic_term GT a2=arith_or_atomic_term
      { Ast.GreaterThan (a1, a2) }
  | a1=arith_or_atomic_term LE a2=arith_or_atomic_term
      { Ast.LessOrEqual (a1, a2) }
  | a1=arith_or_atomic_term GE a2=arith_or_atomic_term
      { Ast.GreaterOrEqual (a1, a2) }
  | a1=atomic_term QUESTION a2=atomic_term COLON a3=atomic_term
      { Ast.ITE (a1, a2, a3) }
  | a1=atomic_term OR a2=atomic_term
      { Ast.Or (a1, a2) }
  | a1=atomic_term AND a2=atomic_term
      { Ast.And (a1, a2) }
  | POINTERCAST a1=atomic_term
      { Ast.IntegerToPointerCast a1 }
  | INTEGERCAST a1=atomic_term
      { Ast.PointerToIntegerCast a1 }
  | a1=atomic_term LBRACKET a2=term RBRACKET
      { Ast.App (a1, a2) }

resource_condition:
  | id_args=pred_with_args name=NAME
      { Ast.{predicate=fst id_args; arguments = snd id_args; oname = Some name} }
  | id_args=pred_with_args 
      { Ast.{predicate=fst id_args; arguments = snd id_args; oname = None} }


cond:
  | c=term
      { Ast.Logical c } 
  | c=resource_condition
      { Ast.Resource c }

