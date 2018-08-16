(* Grammar based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11"

   NOTE: There is a reduce/reduce conflict in the grammar, which is solved
         by reducing to the first production (Menhir's default behaviour).
         See Jourdan's paper.
*)

%{
open Cabs
open Location_ocaml

module LF = Lexer_feedback

let id =
  fun z -> z

let option d f = function
  | Some x -> f x
  | None   -> d

let map_option f = function
  | Some x -> Some (f x)
  | None -> None

let empty_specs =
  { storage_classes= [];
    type_specifiers= [];
    type_qualifiers= [];
    function_specifiers= [];
    alignment_specifiers= [];
  }

let append_specs sp1 sp2 =
  { storage_classes= List.rev_append sp1.storage_classes sp2.storage_classes;
    type_specifiers= List.rev_append sp1.type_specifiers sp2.type_specifiers;
    type_qualifiers= List.rev_append sp1.type_qualifiers sp2.type_qualifiers;
    function_specifiers= List.rev_append sp1.function_specifiers
                          sp2.function_specifiers;
    alignment_specifiers= List.rev_append sp1.alignment_specifiers
                            sp2.alignment_specifiers;
  }

let rec concat_specs = function
  | [] -> empty_specs
  | [spec] -> spec
  | s::ss -> append_specs s (concat_specs ss)

let string_of_cabs_id (Cabs.CabsIdentifier(_, n)) = n


%}

(* §6.4.1 keywords *)
%token AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE ENUM EXTERN
  FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN SHORT SIGNED SIZEOF
  STATIC STRUCT SWITCH TYPEDEF UNION UNSIGNED VOID VOLATILE WHILE ALIGNAS
  ALIGNOF ATOMIC BOOL COMPLEX GENERIC (* IMAGINARY *) NORETURN STATIC_ASSERT
  THREAD_LOCAL

(* §6.4.2 Identifiers *)
%token<string> NAME (* NAME is either an variable identifier or a type name *)
%token VARIABLE TYPE

(* §6.4.4 Constants *)
%token<Cabs.cabs_constant> CONSTANT

(* §6.4.5 String literals *)
%token<Cabs.cabs_string_literal> STRING_LITERAL

(* §6.4.6 Punctuators *)
%token LBRACK RBRACK LPAREN RPAREN LBRACE RBRACE DOT MINUS_GT
  PLUS_PLUS MINUS_MINUS AMPERSAND STAR PLUS MINUS TILDE BANG
  SLASH PERCENT LT_LT GT_GT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET PIPE
  AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON SEMICOLON ELLIPSIS EQ STAR_EQ SLASH_EQ PERCENT_EQ
  PLUS_EQ MINUS_EQ LT_LT_EQ GT_GT_EQ AMPERSAND_EQ CARET_EQ PIPE_EQ COMMA

(* NON-STD: *)
  ASSERT OFFSETOF

(* NON-STD cppmem syntax *)
  LBRACES PIPES RBRACES

%token VA_START VA_ARG PRINT_TYPE

%token EOF

%nonassoc THEN
%nonassoc ELSE

(* ========================================================================== *)

%type<string> typedef_name var_name
%type<Cabs.cabs_identifier> general_identifier

%type<LF.context> save_context

%type<LF.declarator> declarator direct_declarator declarator_varname
  declarator_typedefname

%type<Cabs.cabs_identifier>
  enumeration_constant

%type<Cabs.cabs_expression>
  primary_expression generic_selection postfix_expression unary_expression
  cast_expression multiplicative_expression additive_expression shift_expression
  relational_expression equality_expression _AND_expression
  exclusive_OR_expression inclusive_OR_expression logical_AND_expression
  logical_OR_expression conditional_expression assignment_expression expression
  constant_expression

%type<Cabs.cabs_generic_association list>
  generic_assoc_list
%type<Cabs.cabs_generic_association>
  generic_association

%type<Cabs.cabs_expression list>
  argument_expression_list

%type<Cabs.cabs_unary_operator>
  unary_operator
%type<Cabs.cabs_assignment_operator>
  assignment_operator

%type<Cabs.declaration>
  declaration

%type<Cabs.specifiers>
  declaration_specifiers

%type<Cabs.storage_class_specifier>
  storage_class_specifier

%type<Cabs.cabs_type_specifier>
  struct_or_union_specifier

%type<Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier>
  struct_or_union

%type<Cabs.struct_declaration list>
  struct_declaration_list

%type<Cabs.struct_declaration>
  struct_declaration

%type<Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list>
  specifier_qualifier_list

%type<Cabs.struct_declarator list>
  struct_declarator_list

%type<Cabs.struct_declarator>
  struct_declarator

%type<Cabs.cabs_type_specifier>
  enum_specifier

%type<Cabs.enumerator list>
  enumerator_list

%type<Cabs.enumerator>
  enumerator

%type<Cabs.cabs_type_specifier>
  atomic_type_specifier

%type<Cabs.cabs_type_qualifier>
  type_qualifier

%type<Cabs.function_specifier>
  function_specifier

%type<Cabs.alignment_specifier>
  alignment_specifier

%type<Cabs.pointer_declarator>
  pointer

%type<Cabs.cabs_type_qualifier list>
  type_qualifier_list

%type<Cabs.parameter_declaration list>
  parameter_list

%type<Cabs.parameter_declaration>
  parameter_declaration

%type<Cabs.type_name>
  type_name

%type<Cabs.abstract_declarator>
  abstract_declarator

%type<Cabs.direct_abstract_declarator>
  direct_abstract_declarator

%type<Cabs.initializer_>
  initializer_

%type<((Cabs.designator list) option * Cabs.initializer_) list>
  initializer_list

%type<Cabs.designator list>
  designation

%type<Cabs.designator list>
  designator_list

%type<Cabs.designator>
  designator

%type<Cabs.static_assert_declaration>
  static_assert_declaration

%type<Cabs.cabs_statement>
  statement labeled_statement compound_statement expression_statement
  selection_statement iteration_statement jump_statement

%type<Cabs.cabs_statement list>
  block_item_list

%type<Cabs.cabs_statement>
  block_item

%type<Cabs.external_declaration list>
  external_declaration_list

%type<Cabs.external_declaration>
  external_declaration

%type<Cabs.function_definition>
  function_definition

%start<Cabs.translation_unit> translation_unit

%% (* ======================================================================= *)

translation_unit: (* NOTE: this is not present in the standard *)
| EOF
    { TUnit [] }
| edecls= external_declaration_list EOF
    { TUnit (List.rev edecls) }

(* A pair of lists of exactly one A *)
list_eq1(A, B):
| a=A bs=B*
    { ([a], bs) }
| b=B rest=list_eq1(A, B)
    { let (ax, bs) = rest in (ax, b::bs) }

(* A pair of lists of at least one A *)
list_ge1(A, B):
| a=A bs=B*
    { ([a], bs) }
| a=A rest=list_ge1(A, B)
    { let (ax, bs) = rest in (a::ax, bs) }
| b=B rest=list_ge1(A, B)
    { let (ax, bs) = rest in (ax, b::bs) }

(* A record of lists of exactly one A and one B *)
list_eq1_eq1(A, B, C):
| a=A rest=list_eq1(B, C)
    { let (bs, cs) = rest in ([a], bs, cs) }
| b=B rest=list_eq1(A, C)
    { let (ax, cs) = rest in (ax, [b], cs) }
| c=C rest=list_eq1_eq1(A, B, C)
    { let (ax, bs, cs) = rest in (ax, bs, c::cs) }

(* A record of lists of exactly one A and at least one B *)
list_eq1_ge1(A, B, C):
| a=A rest=list_ge1(B, C)
    { let (bs, cs) = rest in ([a], bs, cs) }
| b=B rest=list_eq1(A, C)
    { let (ax, cs) = rest in (ax, [b], cs) }
| b=B rest=list_eq1_ge1(A, B, C)
    { let (ax, bs, cs) = rest in (ax, b::bs, cs) }
| c=C rest=list_eq1_ge1(A, B, C)
    { let (ax, bs, cs) = rest in (ax, bs, c::cs) }


(* Identifiers and lexer feedback contexts *)

typedef_name:
| n= NAME TYPE
    { n }

var_name:
| n= NAME VARIABLE
    { n }

(* NOTE: This rule is declared early, so that reduce/reduce conflict is
   resolved using it. *)
typedef_name_spec:
| i= typedef_name
  { TSpec ((Location_ocaml.region ($startpos, $endpos) None), TSpec_name (CabsIdentifier (Location_ocaml.point $startpos, i))) }

general_identifier:
| i= typedef_name
| i= var_name
    { CabsIdentifier (Location_ocaml.point $startpos, i) }

save_context:
| (* empty *)
  { LF.save_context () }

scoped(X):
| ctxt=save_context x=X
    { LF.restore_context ctxt; x }

declarator_varname:
| decl = declarator
    { LF.declare_varname (LF.identifier decl); decl }

declarator_typedefname:
| decl = declarator
    { LF.declare_typedefname (LF.identifier decl); decl }


(* §6.4.4.3 Enumeration constants Primary expressions *)
enumeration_constant:
| i= general_identifier
    { LF.declare_varname (string_of_cabs_id i); i }


(* §6.5.1 Primary expressions *)
primary_expression:
| str= var_name
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEident (CabsIdentifier (Location_ocaml.point $startpos(str), str))) }
| cst= CONSTANT
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None, CabsEconst cst) }
| lit= STRING_LITERAL
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None, CabsEstring lit) }
| LPAREN expr= expression RPAREN
    { let CabsExpression (_, expr_) = expr in
      CabsExpression (Location_ocaml.region ($startpos, $endpos) None, expr_ ) }
| gs= generic_selection
    { gs }


(* §6.5.1.1 Generic selection *)
generic_selection:
| GENERIC LPAREN expr= assignment_expression COMMA gas= generic_assoc_list RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEgeneric (expr, gas)) }

generic_assoc_list: (* NOTE: the list is in reverse *)
| ga= generic_association
    { [ga] }
| gas= generic_assoc_list COMMA ga= generic_association
    { ga::gas }

generic_association:
| ty= type_name COLON expr= assignment_expression
    { GA_type (ty, expr) }
| DEFAULT COLON expr= assignment_expression
    { GA_default expr }


(* §6.5.2 Postfix operators *)
postfix_expression:
| expr= primary_expression
    { expr }
| expr1= postfix_expression LBRACK expr2= expression RBRACK
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEsubscript (expr1, expr2)) }
| expr= postfix_expression LPAREN exprs_opt= argument_expression_list? RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEcall (expr, option [] List.rev exprs_opt)) }
| expr= postfix_expression DOT i= general_identifier 
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEmemberof (expr, i)) }
| expr= postfix_expression MINUS_GT i= general_identifier
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEmemberofptr (expr, i)) }
| expr= postfix_expression PLUS_PLUS
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEpostincr expr) }
| expr= postfix_expression MINUS_MINUS
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEpostdecr expr) }
| LPAREN ty= type_name RPAREN LBRACE inits= initializer_list COMMA? RBRACE
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEcompound (ty, List.rev inits)) }
(* NOTE: non-std way of dealing with these *)
| ASSERT LPAREN expr= assignment_expression RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEassert expr) }
| VA_START LPAREN expr= assignment_expression COMMA i= general_identifier RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
        CabsEva_start(expr, i)) }
| VA_ARG LPAREN expr= assignment_expression COMMA ty= type_name RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEva_arg(expr, ty)) }
| OFFSETOF LPAREN ty= type_name COMMA i= general_identifier RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEoffsetof (ty, i)) }
(* NOTE: the following is a cerb extension allowing the user to the
   query the type of an expression  *)
| PRINT_TYPE LPAREN expr= expression RPAREN
   { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
        CabsEprint_type expr) }

argument_expression_list: (* NOTE: the list is in reverse *)
| expr= assignment_expression
    { [expr] }
| exprs= argument_expression_list COMMA expr= assignment_expression
    { expr::exprs }


(* §6.5.3 Unary operators *)
unary_expression:
| expr= postfix_expression
    { expr }
| PLUS_PLUS expr= unary_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($1)),
                      CabsEpreincr expr) }
| MINUS_MINUS expr= unary_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($1)),
                      CabsEpredecr expr) }
| op= unary_operator expr= cast_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos(op)),
                      CabsEunary (op, expr)) }
| SIZEOF expr= unary_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($1)),
                      CabsEsizeof_expr expr) }
| SIZEOF LPAREN ty= type_name RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($1)),
                      CabsEsizeof_type ty) }
| ALIGNOF LPAREN ty= type_name RPAREN
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($1)),
                      CabsEalignof ty) }

unary_operator:
| AMPERSAND
    { CabsAddress }
| STAR
    { CabsIndirection }
| PLUS
    { CabsPlus }
| MINUS
    { CabsMinus }
| TILDE
    { CabsBnot }
| BANG
    { CabsNot }


(* §6.5.4 Cast operators *)
cast_expression:
| expr= unary_expression
    { expr }
| LPAREN ty= type_name RPAREN expr= cast_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) None,
                      CabsEcast (ty, expr)) }


(* §6.5.5 Multiplicative operators *)
multiplicative_expression:
| expr= cast_expression
    { expr }
| expr1= multiplicative_expression STAR expr2= cast_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsMul, expr1, expr2)) }
| expr1= multiplicative_expression SLASH expr2= cast_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsDiv, expr1, expr2)) }
| expr1= multiplicative_expression PERCENT expr2= cast_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsMod, expr1, expr2)) }


(* §6.5.6 Additive operators *)
additive_expression:
| expr= multiplicative_expression
    { expr }
| expr1= additive_expression PLUS expr2= multiplicative_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsAdd, expr1, expr2)) }
| expr1= additive_expression MINUS expr2= multiplicative_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsSub, expr1, expr2)) }


(* §6.5.7 Bitwise shift operators *)
shift_expression:
| expr= additive_expression
    { expr }
| expr1= shift_expression LT_LT expr2= additive_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsShl, expr1, expr2)) }
| expr1= shift_expression GT_GT expr2= additive_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsShr, expr1, expr2)) }


(* §6.5.8 Relational operators *)
relational_expression:
| expr= shift_expression
    { expr }
| expr1= relational_expression LT expr2= shift_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsLt, expr1, expr2)) }
| expr1= relational_expression GT expr2= shift_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsGt, expr1, expr2)) }
| expr1= relational_expression LT_EQ expr2= shift_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsLe, expr1, expr2)) }
| expr1= relational_expression GT_EQ expr2= shift_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsGe, expr1, expr2)) }


(* §6.5.9 Equality operators *)
equality_expression:
| expr= relational_expression
    { expr }
| expr1= equality_expression EQ_EQ expr2= relational_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsEq, expr1, expr2)) }
| expr1= equality_expression BANG_EQ expr2= relational_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsNe, expr1, expr2)) }


(* §6.5.10 Bitwise AND operator *)
_AND_expression:
| expr= equality_expression
    { expr }
| expr1= _AND_expression AMPERSAND expr2= equality_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsBand, expr1, expr2)) }


(* §6.5.11 Bitwise exclusive OR operator *)
exclusive_OR_expression:
| expr= _AND_expression
    { expr }
| expr1= exclusive_OR_expression CARET expr2= _AND_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsBxor, expr1, expr2)) }


(* §6.5.12 Bitwise inclusive OR operator *)
inclusive_OR_expression:
| expr= exclusive_OR_expression
    { expr }
| expr1= inclusive_OR_expression PIPE expr2= exclusive_OR_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsBor, expr1, expr2)) }


(* §6.5.13 Logical AND operator *)
logical_AND_expression:
| expr= inclusive_OR_expression
    { expr }
| expr1= logical_AND_expression AMPERSAND_AMPERSAND expr2= inclusive_OR_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsAnd, expr1, expr2)) }


(* §6.5.14 Logical OR operator *)
logical_OR_expression:
| expr= logical_AND_expression
    { expr }
| expr1= logical_OR_expression PIPE_PIPE expr2= logical_AND_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEbinary (CabsOr, expr1, expr2)) }


(* §6.5.15 Conditional operator *)
conditional_expression:
| expr= logical_OR_expression
    { expr }
| expr1= logical_OR_expression QUESTION expr2= expression COLON expr3= conditional_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEcond (expr1, expr2, expr3)) }


(* §6.5.16 Assignment operators *)
assignment_expression:
| expr= conditional_expression
    { expr }
| expr1= unary_expression op= assignment_operator expr2= assignment_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos(op)),
                      CabsEassign (op, expr1, expr2)) }

assignment_operator:
| EQ
    { Assign  }
| STAR_EQ
    { Assign_Mul }
| SLASH_EQ
    { Assign_Div }
| PERCENT_EQ
    { Assign_Mod }
| PLUS_EQ
    { Assign_Add }
| MINUS_EQ
    { Assign_Sub }
| LT_LT_EQ
    { Assign_Shl }
| GT_GT_EQ
    { Assign_Shr }
| AMPERSAND_EQ
    { Assign_Band }
| CARET_EQ
    { Assign_Bxor }
| PIPE_EQ
    { Assign_Bor }


(* §6.5.17 Comma operator *)
expression:
| expr= assignment_expression
    { expr }
| expr1= expression COMMA expr2= assignment_expression
    { CabsExpression (Location_ocaml.region ($startpos, $endpos) (Some $startpos($2)),
                      CabsEcomma (expr1, expr2)) }

(* §6.6 Constant expressions *)
constant_expression:
| expr= conditional_expression
    { expr }


(* §6.7 Declarations *)
declaration:
| decspecs= declaration_specifiers
    idecls_opt= init_declarator_list(declarator_varname)? SEMICOLON
    { Declaration_base (decspecs, option [] List.rev idecls_opt) }
| decspecs= declaration_specifiers_typedef
    idecls_opt= init_declarator_list(declarator_typedefname)? SEMICOLON
    { Declaration_base (decspecs, option [] List.rev idecls_opt) }
| sa= static_assert_declaration
    { Declaration_static_assert sa }

declaration_specifier:
| sc= storage_class_specifier
    { { empty_specs with storage_classes=      [sc]; } }
| tq= type_qualifier
    { { empty_specs with type_qualifiers=      [tq]; } }
| fs= function_specifier
    { { empty_specs with function_specifiers=  [fs]; } }
| als= alignment_specifier
    { { empty_specs with alignment_specifiers= [als]; } }

declaration_specifiers:
| ts_specs= list_eq1(type_specifier_unique, declaration_specifier)
| ts_specs= list_ge1(type_specifier_nonunique, declaration_specifier)
    { let (ts, ss) = ts_specs in
      { (concat_specs ss) with type_specifiers= ts; } }

declaration_specifiers_typedef:
| ts_specs= list_eq1_eq1(TYPEDEF,type_specifier_unique, declaration_specifier)
| ts_specs= list_eq1_ge1(TYPEDEF,type_specifier_nonunique, declaration_specifier)
    { let (_, ts, ss) = ts_specs in
      let specs = concat_specs ss in
    { specs with storage_classes= SC_typedef::specs.storage_classes;
                 type_specifiers= ts; } }

init_declarator_list(declarator): (* NOTE: the list is in reverse *)
| idecl= init_declarator(declarator)
    { [idecl] }
| idecls= init_declarator_list(declarator)
    COMMA idecl= init_declarator(declarator)
    { idecl::idecls }

init_declarator(declarator):
| decl= declarator
    { InitDecl (Location_ocaml.region ($startpos, $endpos) None,
                LF.cabs_of_declarator decl, None) }
| decl= declarator EQ init= initializer_
    { InitDecl (Location_ocaml.region ($startpos, $endpos) None,
                LF.cabs_of_declarator decl, Some init) }


(* §6.7.1 Storage-class specifiers *)
storage_class_specifier:
(* NOTE: deprived of TYPEDEF, which receives special treatment *)
| EXTERN
    { SC_extern }
| STATIC
    { SC_static }
| THREAD_LOCAL
    { SC_Thread_local }
| AUTO
    { SC_auto }
| REGISTER
    { SC_register }


(* §6.7.2 Type specifiers *)
type_specifier_nonunique:
| CHAR
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_char) }
| SHORT
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_short) }
| INT
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_int) }
| LONG
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_long) }
| FLOAT
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_float) }
| DOUBLE
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_double) }
| SIGNED
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_signed) }
| UNSIGNED
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_unsigned) }
| COMPLEX
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_Complex) }

type_specifier_unique:
| VOID
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_void) }
| BOOL
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_Bool) }
| spec= atomic_type_specifier
    { spec }
| spec= struct_or_union_specifier
    { spec }
| spec= enum_specifier
    { spec }
| spec= typedef_name_spec
    { spec }


(* §6.7.2.1 Structure and union specifiers *)
struct_or_union_specifier:
| ctor= struct_or_union iopt= general_identifier?
    LBRACE rev_decls= struct_declaration_list RBRACE
    { ctor iopt (Some (List.rev rev_decls)) }
| ctor= struct_or_union i= general_identifier
    { ctor (Some i) None }

struct_or_union:
| STRUCT
    { fun x y -> TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_struct (x, y)) }
| UNION
    { fun x y -> TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_union (x, y)) }

struct_declaration_list: (* NOTE: the list is in reverse *)
| sdecl= struct_declaration
    { [sdecl] }
| sdecls= struct_declaration_list sdecl= struct_declaration
    { sdecl::sdecls }

struct_declaration:
| tspecs_tquals= specifier_qualifier_list
    rev_sdeclrs_opt= struct_declarator_list? SEMICOLON
    { let (tspecs, tquals) = tspecs_tquals in
      Struct_declaration (tspecs, tquals, option [] List.rev rev_sdeclrs_opt) }
| sa_decl= static_assert_declaration
    { Struct_assert sa_decl }

specifier_qualifier_list:
| tspecs_tquals= list_eq1 (type_specifier_unique, type_qualifier)
  { tspecs_tquals }
| tspecs_tquals= list_ge1 (type_specifier_nonunique, type_qualifier)
  { tspecs_tquals }

struct_declarator_list: (* NOTE: the list is in reverse *)
| sdelctor= struct_declarator
    { [sdelctor] }
| sdecltors= struct_declarator_list COMMA sdecltor= struct_declarator
    { sdecltor::sdecltors }

struct_declarator:
| decltor= declarator
    { SDecl_simple (LF.cabs_of_declarator decltor) }
| decltor_opt= declarator? COLON expr= constant_expression
    { SDecl_bitfield (map_option LF.cabs_of_declarator decltor_opt, expr) }


(* §6.7.2.2 Enumeration specifiers *)
enum_specifier:
| ENUM iopt= general_identifier? LBRACE enums= enumerator_list COMMA? RBRACE
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_enum (iopt, Some (List.rev enums))) }
| ENUM i= general_identifier
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_enum (Some i, None)) }

enumerator_list: (* NOTE: the list is in reverse *)
| enum= enumerator
    { [enum] }
| enums= enumerator_list COMMA enum= enumerator
    { enum::enums }

enumerator:
| enum_cst= enumeration_constant
    { (enum_cst, None) }
| enum_cst= enumeration_constant EQ expr= constant_expression
    { (enum_cst, Some expr) }


(* §6.7.2.4 Atomic type specifiers *)
atomic_type_specifier:
| ATOMIC LPAREN ty= type_name RPAREN
    { TSpec (Location_ocaml.region ($startpos, $endpos) None, TSpec_Atomic ty) }


(* §6.7.3 Type qualifiers *)
type_qualifier:
| CONST
    { Q_const }
| RESTRICT
    { Q_restrict }
| VOLATILE
    { Q_volatile }
| ATOMIC
    { Q_Atomic }


(* §6.7.4 Function specifiers *)
function_specifier:
| INLINE
    { FS_inline }
| NORETURN
    { FS_Noreturn }


(* §6.7.5 Alignment specifier *)
alignment_specifier:
| ALIGNAS LPAREN ty= type_name RPAREN
    { AS_type ty }
| ALIGNAS LPAREN expr= constant_expression RPAREN
    { AS_expr expr }


(* §6.7.6 Declarators *)

declarator:
| dd= direct_declarator
    { dd }
| pdecl= pointer dd= direct_declarator
    { LF.pointer_decl pdecl dd }

direct_declarator:
| i = general_identifier
    { LF.identifier_decl i }
| LPAREN save_context decltor= declarator RPAREN
    { LF.declarator_decl decltor }
| ddecltor= direct_declarator LBRACK tquals_opt= type_qualifier_list?
  expr_opt= assignment_expression? RBRACK
    { LF.array_decl (ADecl (Location_ocaml.region ($startpos, $endpos) None,
        option [] List.rev tquals_opt, false,
        map_option (fun x -> ADeclSize_expression x) expr_opt)) ddecltor }
| ddecltor= direct_declarator LBRACK STATIC tquals_opt= type_qualifier_list? expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (Location_ocaml.region ($startpos, $endpos) None, option [] List.rev tquals_opt,
        true, Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator LBRACK tquals= type_qualifier_list STATIC
  expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (Location_ocaml.region ($startpos, $endpos) None, List.rev tquals, true,
        Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator LBRACK tquals_opt= type_qualifier_list? STAR RBRACK
    { LF.array_decl (ADecl (Location_ocaml.region ($startpos, $endpos) None, option [] List.rev tquals_opt, false,
        Some ADeclSize_asterisk)) ddecltor }
| ddecltor= direct_declarator LPAREN
  ptys_ctxt= scoped(parameter_type_list) RPAREN
    { let (ptys, ctxt) = ptys_ctxt in LF.fun_decl ptys ctxt ddecltor }
(* TODO: identifier list not supported *)
| ddecltor= direct_declarator LPAREN ctxt=save_context RPAREN
    { LF.fun_decl (Params ([], false)) ctxt ddecltor }
(*
| ddecltor= direct_declarator LPAREN ctxt=save_context identifier_list? RPAREN
    { LF.fun_decl (Params ([], false)) ctxt ddecltor }
*)
(*
identifier_list:
| var_name
| identifier_list COMMA var_name
    {}
*)

pointer:
| STAR tquals= type_qualifier_list? ptr_decltor= pointer?
    { PDecl (Location_ocaml.region ($startpos, $endpos) None, option [] List.rev tquals, ptr_decltor) }

type_qualifier_list: (* NOTE: the list is in reverse *)
| tqual= type_qualifier
    { [tqual] }
| tquals= type_qualifier_list tqual= type_qualifier
    { tqual::tquals }

parameter_type_list:
| param_decls= parameter_list ctxt= save_context
    { (Params (List.rev param_decls, false), ctxt) }
| param_decls= parameter_list COMMA ELLIPSIS ctxt= save_context
    { (Params (List.rev param_decls, true), ctxt)  }

parameter_list: (* NOTE: the list is in reverse *)
| param_decl= parameter_declaration
    { [param_decl] }
| param_decls= parameter_list COMMA param_decl= parameter_declaration
    { param_decl::param_decls }

parameter_declaration:
| specifs= declaration_specifiers decltor= declarator_varname
    { PDeclaration_decl (specifs, LF.cabs_of_declarator decltor) }
| specifs= declaration_specifiers abs_decltor_opt= abstract_declarator?
    { PDeclaration_abs_decl (specifs, abs_decltor_opt) }


(* §6.7.7 Type names *)
type_name:
| tspecs_tquals= specifier_qualifier_list abs_declr_opt= abstract_declarator?
    { let (tspecs, tquals) = tspecs_tquals in
      Type_name (tspecs, tquals, abs_declr_opt) }

abstract_declarator:
| ptr_decltor= pointer
    { AbsDecl_pointer ptr_decltor }
| ptr_decltor_opt= ioption(pointer) dabs_decltor= direct_abstract_declarator
    { AbsDecl_direct (ptr_decltor_opt, dabs_decltor) }


direct_abstract_declarator:
| LPAREN save_context abs_decltor= abstract_declarator RPAREN
  { DAbs_abs_declarator abs_decltor }
| dabs_decltor= direct_abstract_declarator? LBRACK
  tquals= ioption(type_qualifier_list) expr= assignment_expression? RBRACK
  { DAbs_array (dabs_decltor, ADecl (Location_ocaml.unknown, option [] id tquals,
      false, option None (fun e -> Some (ADeclSize_expression e)) expr)) }
| dabs_decltor= direct_abstract_declarator? LBRACK STATIC
  tquals= type_qualifier_list? expr= assignment_expression RBRACK
  { DAbs_array (dabs_decltor, ADecl (Location_ocaml.unknown, option [] id tquals,
      true, Some (ADeclSize_expression expr))) }
| dabs_decltor= direct_abstract_declarator? LBRACK
  tquals= type_qualifier_list STATIC expr= assignment_expression RBRACK
  { DAbs_array (dabs_decltor, ADecl (Location_ocaml.unknown, tquals, true,
      Some (ADeclSize_expression expr))) }
| dabs_decltor= direct_abstract_declarator? LBRACK STAR RBRACK
  { DAbs_array (dabs_decltor, ADecl (Location_ocaml.unknown, [], false,
      Some ADeclSize_asterisk)) }
| dabs_decltor= ioption(direct_abstract_declarator) LPAREN
    param_tys_ctxt_opt = scoped(parameter_type_list)? RPAREN
  { match param_tys_ctxt_opt with
    | Some (param_tys, _) ->
      DAbs_function (dabs_decltor, param_tys)
    | None ->
      DAbs_function (dabs_decltor, Params ([], false)) }


(* §6.7.8 Type definitions *)


(* §6.7.9 Initialization *)
initializer_:
| expr= assignment_expression
    { Init_expr expr }
| LBRACE inits= initializer_list RBRACE
| LBRACE inits= initializer_list COMMA RBRACE
    { Init_list (List.rev inits) }

initializer_list: (* NOTE: the list is in reverse *)
| design_opt= designation? init= initializer_
    { [(design_opt, init)] }
| inits= initializer_list COMMA design_opt= designation? init= initializer_
    { (design_opt, init)::inits }

designation:
| design= designator_list EQ
    { List.rev design }

designator_list: (* NOTE: the list is in reverse *)
| design= designator
    { [design] }
| designs= designator_list design= designator
    { design::designs }

designator:
| LBRACK expr= constant_expression RBRACK
    { Desig_array expr }
| DOT i= general_identifier
    { Desig_member i }

(* §6.7.10 Static assertions *)
static_assert_declaration:
| STATIC_ASSERT LPAREN expr= constant_expression COMMA
  lit= STRING_LITERAL RPAREN SEMICOLON
    { Static_assert (expr, lit) }


(* §6.8 Statements and blocks *)
statement:
| stmt= labeled_statement
| stmt= scoped(compound_statement)
| stmt= expression_statement
| stmt= scoped(selection_statement)
| stmt= scoped(iteration_statement)
| stmt= jump_statement
  { stmt }
;

(* §6.8.1 Labeled statements *)
labeled_statement:
| i= general_identifier COLON stmt= statement
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
        CabsSlabel (i, stmt)) }
| CASE expr= constant_expression COLON stmt= statement
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
        CabsScase (expr, stmt)) }
| DEFAULT COLON stmt= statement
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None, CabsSdefault stmt) }
;

(* §6.8.2 Compound statement *)
compound_statement:
| LBRACE bis_opt= block_item_list? RBRACE
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
        CabsSblock (option [] List.rev bis_opt)) }
(* NON-STD cppmem syntax *)
| LBRACES stmts= separated_nonempty_list(PIPES, statement) RBRACES
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None, CabsSpar stmts) }
;

block_item_list: (* NOTE: the list is in reverse *)
| stmt= block_item
    { [stmt] }
| stmts= block_item_list stmt= block_item
    { stmt::stmts }

block_item:
| decl= declaration
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None, CabsSdecl decl) }
| stmt= statement
    { stmt }
;

(* §6.8.3 Expression and null statements *)
expression_statement:
| expr_opt= expression? SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     option CabsSnull (fun z -> CabsSexpr z) expr_opt) }
;


(* §6.8.4 Selection statements *)
selection_statement:
| IF LPAREN expr= expression RPAREN stmt= scoped(statement) %prec THEN
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSif (expr, stmt, None)) }
| IF LPAREN expr= expression RPAREN stmt1= scoped(statement)
  ELSE stmt2= scoped(statement)
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSif (expr, stmt1, Some stmt2)) }
| SWITCH LPAREN expr= expression RPAREN stmt= scoped(statement)
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSswitch (expr, stmt)) }
;

(* §6.8.5 Iteration statements *)
iteration_statement:
| WHILE LPAREN expr= expression RPAREN stmt= scoped(statement)
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSwhile (expr, stmt)) }
| DO stmt= scoped(statement) WHILE LPAREN expr= expression RPAREN SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSdo (expr, stmt)) }
| FOR LPAREN expr1_opt= expression? SEMICOLON expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN stmt= scoped(statement)
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSfor (map_option (fun x -> FC_expr x) expr1_opt,
                               expr2_opt,expr3_opt, stmt)) }
| FOR LPAREN decl= declaration expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN stmt= scoped(statement)
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSfor (Some (FC_decl decl), expr2_opt, expr3_opt,
                               stmt)) }
;


(* §6.8.6 Jump statements *)
jump_statement:
| GOTO i= general_identifier SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSgoto i) }
| CONTINUE SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None, CabsScontinue) }
| BREAK SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None, CabsSbreak) }
| RETURN expr_opt= expression? SEMICOLON
    { CabsStatement (Location_ocaml.region ($startpos, $endpos) None,
                     CabsSreturn expr_opt) }
;


(* §6.9 External definitions *)
external_declaration_list: (* NOTE: the list is in reverse *)
| def= external_declaration
    { [def] }
| defs= external_declaration_list def= external_declaration
    { def :: defs }

external_declaration:
| fdef= function_definition
    { EDecl_func fdef }
| decl= declaration
    { EDecl_decl decl }


(* §6.9.1 Function definitions *)
function_definition1:
| specifs= declaration_specifiers decltor= declarator_varname
  { let ctxt = LF.save_context () in
    LF.reinstall_function_context decltor;
    (specifs, decltor, ctxt)
  }

function_definition:
(* TODO: declaration list not supported *)
| specifs_decltor_ctxt= function_definition1 declaration_list?
  stmt= compound_statement
  { let (specifs, decltor, ctxt) = specifs_decltor_ctxt in
    LF.restore_context ctxt;
    (* NOTE: when dugaring to Ail we add to following location the marker for
       the function identifier *)
    FunDef ( Location_ocaml.region ($startpos, $endpos) None
           , specifs, LF.cabs_of_declarator decltor, stmt)
  }

declaration_list:
| declaration
| declaration_list declaration
{}
