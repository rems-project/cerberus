%{
(* adapting from core_parser.mly *)
open Assertion_parser_util
%}


%token <Z.t> Z
%token <string> NAME

%token PLUS
%token MINUS
%token STAR
%token SLASH
%token POWER

%token PLUSDOT
%token MINUSDOT
%token STARDOT

%token EQ
%token NE
%token LT
%token GT
%token LE
%token GE

%token LPAREN
%token RPAREN
%token COMMA

%token POINTERCAST

%token AMPERSAND
%token AT

%token EOF

/* STAR? */
%left EQ NE GT LT GE LE
%left PLUS MINUS PLUSDOT MINUSDOT
%left STAR STARDOT SLASH
/* %nonassoc POWER */

%type <Ast.term>term
%type <Ast.condition>cond
%type <Ast.condition>start

%start start

%%


start:
  | cond=cond EOF
      { cond }

labeled_name:
  | id=NAME
      { Path.LabeledName.{label = None; v = id } }
  | id=NAME AT label=NAME
      { Path.LabeledName.{label = Some label; v = id } }



path:
  | AMPERSAND id=NAME
      { Path.Addr id }
  | ln=labeled_name
      { Path.Var ln }
  | STAR p=path
      { Path.Pointee p }

predarg:
  | p=path
      { Path.PathArg p }
  | a1=predarg PLUS a2=predarg
      { Path.Add (a1, a2) }
  | a1=predarg MINUS a2=predarg
      { Path.Sub (a1, a2) }
  | a1=predarg PLUSDOT a2=predarg
      { Path.AddPointer (a1, a2) }
  | a1=predarg MINUSDOT a2=predarg
      { Path.SubPointer (a1, a2) }
  | a1=predarg STARDOT a2=predarg
      { Path.MulPointer (a1, a2) }
  | POINTERCAST a1 = predarg
      { Path.IntegerToPointerCast a1 }
  | z=Z
      { Path.NumArg z }



%inline resource_condition:
  | id=NAME args=delimited(LPAREN, separated_list(COMMA, predarg), RPAREN)
      { Ast.{predicate=id; arguments = args} }

term_or_path:
  | t=term
      { t }
  | p=path
      { Ast.Path p }


term:
  | POWER LPAREN a1=term_or_path COMMA a2=term_or_path RPAREN
      { Ast.ArithOp (Exponentiation (a1, a2)) }
  | t=delimited(LPAREN, term_or_path, RPAREN)
      { t }
  | z=Z
      { Ast.Lit (Integer z) }
  | a1=term_or_path PLUS a2=term_or_path
      { Ast.ArithOp (Addition (a1, a2)) }
  | a1=term_or_path MINUS a2=term_or_path
      { Ast.ArithOp (Subtraction (a1, a2)) }
  | a1=term_or_path STAR a2=term_or_path
      { Ast.ArithOp (Multiplication (a1, a2)) }
  | a1=term_or_path SLASH a2=term_or_path
      { Ast.ArithOp (Division (a1, a2)) }
  | a1=term_or_path EQ a2=term_or_path
      { Ast.CmpOp (Equality (a1, a2)) }
  | a1=term_or_path NE a2=term_or_path
      { Ast.CmpOp (Inequality (a1, a2)) }
  | a1=term_or_path LT a2=term_or_path
      { Ast.CmpOp (LessThan (a1, a2)) }
  | a1=term_or_path GT a2=term_or_path
      { Ast.CmpOp (GreaterThan (a1, a2)) }
  | a1=term_or_path LE a2=term_or_path
      { Ast.CmpOp (LessOrEqual (a1, a2)) }
  | a1=term_or_path GE a2=term_or_path
      { Ast.CmpOp (GreaterOrEqual (a1, a2)) }

%inline cond:
  | c=term
      { Ast.Logical c } 
  | c=resource_condition
      { Ast.Resource c }

