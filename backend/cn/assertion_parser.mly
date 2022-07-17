%{
(* adapting from core_parser.mly *)
open Assertion_parser_util
%}


%token <Z.t> Z
%token <string> LNAME
%token <string> UNAME



%token TRUE
%token FALSE

%token LET
%token EQUAL
%token UNCHANGED

%token <string> MEMBER

%token PLUS
%token MINUS
%token STAR
%token SLASH


%token EQ
%token NE
%token LT
%token GT
%token LE
%token GE

%token ARROW

%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE

%token COMMA
%token SEMICOLON

%token QUESTION
%token COLON
%token OR
%token AND
%token NOT

%token NULL
%token OFFSETOF
%token POINTERCAST
%token INTEGERCAST
%token POINTER
%token INTEGER
%token DISJOINT

%token CELLPOINTER



%token AMPERSAND
%token AT

%token EACH
%token FOR


%token TYPEOF
%token IF
%token STRUCT


%token TRUSTED
%token ACCESSES
%token REQUIRES
%token ENSURES
%token INV



%token EOF

/* %left EQ NE GT LT GE LE */
%left AND
%left PLUS MINUS
%left STAR SLASH
/* %nonassoc POINTERCAST */
%nonassoc MEMBER /* PREDARG */


%type <Ast.term>term
%type <Ast.condition>cond
%type <Ast.condition>start
%type <Ast.keyword_condition>keyword_condition
%type <Z.t>integer

%start start integer keyword_condition

%%


start:
  | cond=cond EOF
      { cond }



%inline name:
  | n=LNAME
      { n }
  | n=UNAME
      { n }

%inline args:
  | LPAREN args=separated_list(COMMA, term) RPAREN
      { args }


integer:
  | MINUS z=Z
      { Z.neg z }
  | z=Z
      { z }
  | LPAREN z=integer RPAREN
      { z }


/* taking the location-handling aspect from c_parser.mly */
member:
  | m=MEMBER
     { Id.parse (Location_ocaml.(region ($startpos, $endpos) (PointCursor $startpos(m)))) m }

/* taking the location-handling aspect from c_parser.mly */
id:
  | i=name
     { Id.parse (Location_ocaml.(region ($startpos, $endpos) (PointCursor $startpos(i)))) i }




atomic_term:
  | LPAREN t= term RPAREN
      { t }
  | TRUE
      { Ast.Bool true }
  | FALSE
      { Ast.Bool false }
  | z=Z
      { Ast.Integer z }
  | a1=atomic_term m=member
      { Ast.Member (a1, m) }
  | a1=UNAME m=member
      { Ast.Member (Var a1, m) }
  | AMPERSAND id=name
      { Ast.Addr id }
  | v=LNAME
      { Ast.Var v }
  | STAR p=atomic_term
      { Ast.Pointee p }
  | NULL
      { Ast.Null }
  | OFFSETOF LPAREN tag = name COMMA member= name RPAREN
      { Ast.OffsetOf {tag; member} }
  | AMPERSAND LPAREN t=atomic_term ARROW member= name RPAREN
      { Ast.MemberShift {pointer=t; member} }
  | AMPERSAND LPAREN t=atomic_term LBRACKET index=  term RBRACKET RPAREN
      { Ast.ArrayShift {pointer=t; index} }
  | CELLPOINTER LPAREN t1=term COMMA t2=term COMMA t3=term COMMA t4=term COMMA t5=term RPAREN
      { Ast.CellPointer ((t1, t2), (t3, t4), t5) }
  | LBRACE a=term RBRACE AT l=name
      { Ast.Env (a, l) }
  | LBRACE t=term RBRACE UNCHANGED
      { Ast.Unchanged t }
  | t=name UNCHANGED
      { Ast.Unchanged (Var t) }
  /* | LBRACE RBRACE t=term */
  /*     { Ast.PredEqRegulator ([], t) } */
  /* | LBRACE SLASH names=separated_list(COMMA, name) RBRACE t=term */
  /*     { Ast.PredEqRegulator (names, t) } */
  | DISJOINT LPAREN p1=term COMMA sz1=term COMMA p2=term COMMA sz2=term RPAREN
      { Ast.Disjoint ((p1, sz1), (p2, sz2)) }
  | FOR LPAREN i = integer COMMA s = name COMMA j = integer RPAREN LBRACE body=term RBRACE
      { Ast.For ((i, s, j), body) }

arith_term:
  | a1=arith_or_atomic_term PLUS a2=arith_or_atomic_term
      { Ast.Addition (a1, a2) }
  | a1=arith_or_atomic_term MINUS a2=arith_or_atomic_term
      { Ast.Subtraction (a1, a2) } 
  | a1=arith_or_atomic_term STAR a2=arith_or_atomic_term
      { Ast.Multiplication (a1, a2) }
  | a1=arith_or_atomic_term SLASH a2=arith_or_atomic_term
      { Ast.Division (a1, a2) }
  | t=atomic_term LBRACE member=MEMBER EQUAL v=atomic_term RBRACE
      { Ast.StructUpdate ((t, Id.id member), v) }
  | t=atomic_term LBRACKET i=atomic_term EQUAL v=atomic_term RBRACKET
      { Ast.ArraySet ((t, i), v) }

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
  | a1=term AND a2=term
      { Ast.And (a1, a2) }
  | NOT LPAREN t=term RPAREN
      { Ast.Not t }
  | POINTERCAST a1=atomic_term
      { Ast.IntegerToPointerCast a1 }
  | INTEGERCAST a1=atomic_term
      { Ast.PointerToIntegerCast a1 }
  | a1=atomic_term LBRACKET a2=term RBRACKET
      { Ast.App (a1, a2) } 
  | predicate = LNAME arguments = args
      { Ast.Pred (predicate, arguments) }






basetype:
  | POINTER
      { BaseTypes.Loc }
  | INTEGER
      { BaseTypes.Integer }
  

ctype:
  | TYPEOF LPAREN t=term RPAREN
      { Ast.Typeof t }
  | STRUCT name=name
      { Ast.Struct name }
  | ct=ctype STAR
      { Ast.Pointer ct }

%inline ctype_annotation:
  | LT typ=ctype GT
      { typ }

%inline if_permission_clause:
  | IF t=term
      { t }





logicalconstraint:
  | c=term
      { (None, c) }
  | EACH LPAREN bt=basetype qname=name SEMICOLON t=term RPAREN LBRACE c=term RBRACE
      { 
        (Some (qname,bt,t), c)
      }


resource:
  | predicate=UNAME maybe_typ=option(ctype_annotation) arguments=args maybe_permission=option(if_permission_clause)
      { 
        Ast.{oq = None; predicate; arguments; o_permission = maybe_permission; typ = maybe_typ}
      }
  | EACH LPAREN bt=basetype qname=name SEMICOLON t=term RPAREN LBRACE predicate=UNAME maybe_typ=option(ctype_annotation) arguments=args maybe_permission=option(if_permission_clause) RBRACE
      { 
        Ast.{oq = Some (qname,bt,t); predicate; arguments; o_permission = maybe_permission; typ = maybe_typ}
      }




cond:
  | c=logicalconstraint
      { Ast.Constraint (fst c, snd c) } 
  | LET name=UNAME EQUAL r=resource
      { Ast.Resource (name, r) }
  | LET id=LNAME EQUAL t=term
      { Ast.Define (id, t) }

/* taking the location-handling aspect from c_parser.mly */
cond_with_loc:
  | c=cond
      { ((Location_ocaml.(region ($startpos, $endpos) (PointCursor $startpos(c)))), c) }


keyword_condition:
  | ACCESSES a=separated_list(SEMICOLON, id) EOF
     { Accesses a }
  | TRUSTED EOF
     { Trusted }
  | REQUIRES c=separated_list(SEMICOLON, cond_with_loc) EOF
     { Ast.Requires c }
  | ENSURES c=separated_list(SEMICOLON, cond_with_loc) EOF
     { Ast.Ensures c }
  | INV c=separated_list(SEMICOLON, cond_with_loc) EOF
     { Ast.Inv c }
