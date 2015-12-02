%{
open Cabs

let id =
  fun z -> z

let option d f = function
  | Some z -> f z
  | None   -> d


let empty_specs = {
  storage_classes= [];
  type_specifiers= [];
  type_qualifiers= [];
  function_specifiers= [];
  alignment_specifiers= [];
}


%}


(* §6.4.1 keywords *)
%token AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE ENUM EXTERN
  FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN SHORT SIGNED SIZEOF
  STATIC STRUCT SWITCH TYPEDEF UNION UNSIGNED VOID VOLATILE WHILE ALIGNAS
  ALIGNOF ATOMIC BOOL COMPLEX GENERIC (* IMAGINARY *) NORETURN STATIC_ASSERT
  THREAD_LOCAL
  ATOMIC_LPAREN (* this is a hack to solve a grammar ambiguity (see Lexer.mll) *)

(* §6.4.2 Identifiers *)
%token<Cabs.identifier> VAR_NAME2 TYPEDEF_NAME2 OTHER_NAME

(* §6.4.4 Constants *)
%token<Cabs.constant> CONSTANT

(* §6.4.5 String literals *)
%token<string> STRING_LITERAL

(* §6.4.6 Punctuators *)
%token LBRACKET RBRACKET LPAREN RPAREN LBRACE RBRACE DOT MINUS_GT
  PLUS_PLUS MINUS_MINUS AMPERSAND STAR PLUS MINUS TILDE BANG
  SLASH PERCENT LT_LT GT_GT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET PIPE AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON SEMICOLON ELLIPSIS
  EQ STAR_EQ SLASH_EQ PERCENT_EQ PLUS_EQ MINUS_EQ LT_LT_EQ GT_GT_EQ AMPERSAND_EQ CARET_EQ PIPE_EQ
  COMMA (* TODO: HASH HASH_HASH *)
(* TODO(in lexer?)  LT_COLON COLON_GT LT_PERCENT PERCENT_GT PERCENT_COLON PERCENT_COLON_PERCENT_COLON *)

%token EOF

(* ========================================================================== *)

%type<Cabs.identifier>
  enumeration_constant

%type<Cabs.expression>
  primary_expression generic_selection postfix_expression unary_expression
  cast_expression multiplicative_expression additive_expression shift_expression
  relational_expression equality_expression _AND_expression
  exclusive_OR_expression inclusive_OR_expression logical_AND_expression
  logical_OR_expression conditional_expression assignment_expression expression
  constant_expression

%type<Cabs.generic_association list>
  generic_assoc_list
%type<Cabs.generic_association>
  generic_association

%type<Cabs.expression list>
  argument_expression_list

%type<Cabs.unary_operator>
  unary_operator
%type<Cabs.assignment_operator>
  assignment_operator

%type<Cabs.declaration>
  declaration

%type<Cabs.specifiers>
  declaration_specifiers

%type<Cabs.init_declarator list>
  init_declarator_list

%type<Cabs.init_declarator>
  init_declarator

%type<Cabs.storage_class_specifier>
  storage_class_specifier

%type<Cabs.type_specifier>
  type_specifier

%type<Cabs.type_specifier>
  struct_or_union_specifier

%type<identifier option -> (Cabs.struct_declaration list) option -> Cabs.type_specifier>
  struct_or_union

%type<Cabs.struct_declaration list>
  struct_declaration_list

%type<Cabs.struct_declaration>
  struct_declaration

%type<Cabs.type_specifier list * Cabs.type_qualifier list>
  specifier_qualifier_list

%type<Cabs.struct_declarator list>
  struct_declarator_list

%type<Cabs.struct_declarator>
  struct_declarator

%type<Cabs.type_specifier>
  enum_specifier

%type<Cabs.enumerator list>
  enumerator_list

%type<Cabs.enumerator>
  enumerator

%type<Cabs.type_specifier>
  atomic_type_specifier

%type<Cabs.type_qualifier>
  type_qualifier

%type<Cabs.function_specifier>
  function_specifier

%type<Cabs.alignment_specifier>
  alignment_specifier

%type<Cabs.declarator>
  declarator

%type<Cabs.direct_declarator>
  direct_declarator

%type<Cabs.pointer_declarator>
  pointer

%type<Cabs.type_qualifier list>
  type_qualifier_list

%type<Cabs.parameter_type_list>
  parameter_type_list

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

%type<Cabs.statement>
  statement_dangerous statement_safe  labeled_statement(statement_safe)
  labeled_statement(statement_dangerous) iteration_statement(statement_safe)
  iteration_statement(statement_dangerous) compound_statement
  expression_statement selection_statement_dangerous selection_statement_safe
  iteration_statement(last_statement) jump_statement

%type<Cabs.statement list>
  block_item_list

%type<Cabs.statement>
  block_item

%type<Cabs.declaration list>
  translation_unit

%type<Cabs.declaration>
  external_declaration

%type<Cabs.declaration>
  function_definition





%start<Cabs.declaration list> translation_unit_file

%% (* ======================================================================= *)

translation_unit_file: (* NOTE: this is not present in the standard *)
| defs= translation_unit EOF
    { List.rev defs }







(* §6.4.4.3 Enumeration constants Primary expressions *)
enumeration_constant:
| cst= VAR_NAME2
    { cst }


(* §6.5.1 Primary expressions *)
primary_expression:
| id= VAR_NAME2
    { Eident id }
| cst= CONSTANT
    { Econst cst }
| LPAREN expr= expression RPAREN
    { expr }
| gs= generic_selection
    { gs }


(* §6.5.1.1 Generic selection *)
generic_selection:
|  GENERIC LPAREN expr= assignment_expression COMMA gas= generic_assoc_list RPAREN
    { Egeneric (expr, gas) }

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
| expr1= postfix_expression LBRACKET expr2= expression RBRACKET
    { Esubscript (expr1, expr2) }
| expr= postfix_expression LPAREN exprs_opt= argument_expression_list? RPAREN
    { Ecall (expr, option [] List.rev exprs_opt) }
| expr= postfix_expression DOT id= OTHER_NAME
    { Ememberof (expr, id) }
| expr= postfix_expression MINUS_GT id= OTHER_NAME
    { Ememberofptr (expr, id) }
| expr= postfix_expression PLUS_PLUS
    { Epostincr expr }
| expr= postfix_expression MINUS_MINUS
    { Epostdecr expr }
| LPAREN ty= type_name RPAREN LBRACE inits= initializer_list RBRACE
| LPAREN ty= type_name RPAREN LBRACE inits= initializer_list COMMA RBRACE
    { Ecompound (ty, List.rev inits) }

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
    { Epreincr expr }
| MINUS_MINUS expr= unary_expression
    { Epredecr expr }
| op= unary_operator expr= cast_expression
    { Eunary (op, expr) }
| SIZEOF expr= unary_expression
    { Esizeof_expr expr }
| SIZEOF LPAREN ty= type_name RPAREN
    { Esizeof_type ty }
| ALIGNOF LPAREN ty= type_name RPAREN
    { Ealignof ty }

unary_operator:
| AMPERSAND
    { Address }
| STAR
    { Indirection } 
| PLUS
    { Plus }
| MINUS
    { Minus }
| TILDE
    { Bnot }
| BANG
    { Not }


(* §6.5.4 Cast operators *)
cast_expression:
| expr= unary_expression
    { expr }
| LPAREN ty= type_name RPAREN expr= cast_expression
    { Ecast (ty, expr) }


(* §6.5.5 Multiplicative operators *)
multiplicative_expression:
| expr= cast_expression
    { expr }
| expr1= multiplicative_expression STAR expr2= cast_expression
    { Ebinary (Mul, expr1, expr2) }
| expr1= multiplicative_expression SLASH expr2= cast_expression
    { Ebinary (Div, expr1, expr2) }
| expr1= multiplicative_expression PERCENT expr2= cast_expression
    { Ebinary (Mod, expr1, expr2) }


(* §6.5.6 Additive operators *)
additive_expression:
| expr= multiplicative_expression
    { expr }
| expr1= additive_expression PLUS expr2= multiplicative_expression
    { Ebinary (Add, expr1, expr2) }
| expr1= additive_expression MINUS expr2= multiplicative_expression
    { Ebinary (Sub, expr1, expr2) }


(* §6.5.7 Bitwise shift operators *)
shift_expression:
| expr= additive_expression
    { expr }
| expr1= shift_expression LT_LT expr2= additive_expression
    { Ebinary (Shl, expr1, expr2) }
| expr1= shift_expression GT_GT expr2= additive_expression
    { Ebinary (Shr, expr1, expr2) }


(* §6.5.8 Relational operators *)
relational_expression:
| expr= shift_expression
    { expr }
| expr1= relational_expression LT expr2= shift_expression
    { Ebinary (Lt, expr1, expr2) }
| expr1= relational_expression GT expr2= shift_expression
    { Ebinary (Gt, expr1, expr2) }
| expr1= relational_expression LT_EQ expr2= shift_expression
    { Ebinary (Le, expr1, expr2) }
| expr1= relational_expression GT_EQ expr2= shift_expression
    { Ebinary (Ge, expr1, expr2) }


(* §6.5.9 Equality operators *)
equality_expression:
| expr= relational_expression
    { expr }
| expr1= equality_expression EQ_EQ expr2= relational_expression
    { Ebinary (Eq, expr1, expr2) }
| expr1= equality_expression BANG_EQ expr2= relational_expression
    { Ebinary (Ne, expr1, expr2) }


(* §6.5.10 Bitwise AND operator *)
_AND_expression:
| expr= equality_expression
    { expr }
| expr1= _AND_expression AMPERSAND expr2= equality_expression
    { Ebinary (Band, expr1, expr2) }


(* §6.5.11 Bitwise exclusive OR operator *)
exclusive_OR_expression:
| expr= _AND_expression
    { expr }
| expr1= exclusive_OR_expression CARET expr2= _AND_expression
    { Ebinary (Bxor, expr1, expr2) }


(* §6.5.12 Bitwise inclusive OR operator *)
inclusive_OR_expression:
| expr= exclusive_OR_expression
    { expr }
| expr1= inclusive_OR_expression PIPE expr2= exclusive_OR_expression
    { Ebinary (Bor, expr1, expr2) }


(* §6.5.13 Logical AND operator *)
logical_AND_expression:
| expr= inclusive_OR_expression
    { expr }
| expr1= logical_AND_expression AMPERSAND_AMPERSAND expr2= inclusive_OR_expression
    { Ebinary (And, expr1, expr2) }


(* §6.5.14 Logical OR operator *)
logical_OR_expression:
| expr= logical_AND_expression
    { expr }
| expr1= logical_OR_expression PIPE_PIPE expr2= logical_AND_expression
    { Ebinary (Or, expr1, expr2) }


(* §6.5.15 Conditional operator *)
conditional_expression:
| expr= logical_OR_expression
    { expr }
| expr1= logical_OR_expression QUESTION expr2= expression COLON expr3= conditional_expression
    { Econd (expr1, expr2, expr3) }


(* §6.5.16 Assignment operators *)
assignment_expression:
| expr= conditional_expression
    { expr }
| expr1= unary_expression op= assignment_operator expr2= assignment_expression
    { Eassign (op, expr1, expr2) }

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
    { Ecomma (expr1, expr2) }


(* §6.6 Constant expressions *)
constant_expression:
| expr= conditional_expression
    { expr }


(* §6.7 Declarations *)
declaration:
| decspecs= declaration_specifiers idecls= init_declarator_list? SEMICOLON
    { failwith "TODO" } (* DECDEF ((fst decspec, List.rev decls), snd decspec) *)
| sa= static_assert_declaration
    { failwith "TODO" }

declaration_specifiers:
| sc= storage_class_specifier specs_opt= declaration_specifiers?
    { let specs = option empty_specs id specs_opt in
      { specs with storage_classes= sc :: specs.storage_classes }
    }
| tspec= type_specifier specs_opt= declaration_specifiers?
    { let specs = option empty_specs id specs_opt in
      { specs with type_specifiers= tspec :: specs.type_specifiers }
    }
| tqual= type_qualifier specs_opt= declaration_specifiers?
    { let specs = option empty_specs id specs_opt in
      { specs with type_qualifiers= tqual :: specs.type_qualifiers }
    }
| fspec= function_specifier specs_opt= declaration_specifiers?
    { let specs = option empty_specs id specs_opt in
      { specs with function_specifiers= fspec :: specs.function_specifiers }
    }
| aspec= alignment_specifier specs_opt= declaration_specifiers?
    { let specs = option empty_specs id specs_opt in
      { specs with alignment_specifiers= aspec :: specs.alignment_specifiers }
    }

init_declarator_list: (* NOTE: the list is in reverse *)
| idecl= init_declarator
    { [idecl] }
| idecls= init_declarator_list COMMA idecl= init_declarator
    { idecl::idecls }

init_declarator:
| decl= declarator
    { InitDecl (decl, None) }
| decl= declarator EQ init= initializer_
    { InitDecl (decl, Some init) }


(* §6.7.1 Storage-class specifiers *)
storage_class_specifier:
| TYPEDEF
    { SC_typedef }
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
type_specifier:
| VOID
    { TSpec_void }
| CHAR
    { TSpec_char }
| SHORT
    { TSpec_short }
| INT
    { TSpec_int }
| LONG
    { TSpec_long }
| FLOAT
    { TSpec_float }
| DOUBLE
    { TSpec_double }
| SIGNED
    { TSpec_signed }
| UNSIGNED
    { TSpec_unsigned }
| BOOL
    { TSpec_Bool }
| COMPLEX
    { TSpec_Complex }
| spec= atomic_type_specifier
    { spec }
| spec= struct_or_union_specifier
    { spec }
| spec= enum_specifier
    { spec }
| id= TYPEDEF_NAME2
    { TSpec_name id }


(* §6.7.2.1 Structure and union specifiers *)
struct_or_union_specifier:
| ctor= struct_or_union id_opt= OTHER_NAME? LBRACE decls= struct_declaration_list RBRACE
    {  ctor id_opt (Some (List.rev decls)) }
| ctor= struct_or_union id= OTHER_NAME
    { ctor (Some id) None }

struct_or_union:
| STRUCT
    { fun x y -> TSpec_struct (x, y) }
| UNION
    { fun x y -> TSpec_union (x, y) }

struct_declaration_list: (* NOTE: the list is in reverse *)
| sdecl= struct_declaration
    { [sdecl] }
| sdecls= struct_declaration_list sdecl= struct_declaration
    { sdecl::sdecls }

struct_declaration:
| tspecs_qs= specifier_qualifier_list sdeclrs_opt= struct_declarator_list? SEMICOLON
    { let (tspecs, qs) = tspecs_qs in Struct_declaration (tspecs, qs, option [] id sdeclrs_opt) }
| sa_decl= static_assert_declaration
    { Struct_assert sa_decl }

specifier_qualifier_list:
| tspec= type_specifier tspecs_qs_opt= specifier_qualifier_list?
    {
      let (tspecs, qs) = option ([],[]) id tspecs_qs_opt in
      (tspec::tspecs, qs)
    }
| tqual= type_qualifier tspecs_qs_opt= specifier_qualifier_list?
    {
      let (tspecs, qs) = option ([],[]) id tspecs_qs_opt in
      (tspecs, tqual::qs)
    }

struct_declarator_list: (* NOTE: the list is in reverse *)
| sdelctor= struct_declarator
    { [sdelctor] }

| sdecltors= struct_declarator_list COMMA sdecltor= struct_declarator
    { sdecltor::sdecltors }

struct_declarator:
| decltor= declarator
    { SDecl_simple decltor }
| decltor_opt= declarator? COLON expr= constant_expression
    { SDecl_bitfield (decltor_opt, expr) }


(* §6.7.2.2 Enumeration specifiers *)
enum_specifier:
| ENUM id_opt= OTHER_NAME? LBRACE enums= enumerator_list RBRACE
| ENUM id_opt= OTHER_NAME? LBRACE enums= enumerator_list COMMA RBRACE
    { TSpec_enum (id_opt, Some (List.rev enums)) }
| ENUM id= OTHER_NAME
    { TSpec_enum (Some id, None)  }

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
| ATOMIC_LPAREN ty= type_name RPAREN
    { TSpec_Atomic ty }


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
| ptr_opt= pointer? ddecltor= direct_declarator
    { Declarator (ptr_opt, ddecltor) }

direct_declarator:
| id= VAR_NAME2
    { DDecl_identifier id }
| LPAREN decltor= declarator RPAREN
    { DDecl_declarator decltor }
| ddecltor= direct_declarator LBRACKET qs_opt= type_qualifier_list? expr_opt= assignment_expression? RBRACKET
    { DDecl_array (ddecltor, ADecl (option [] id qs_opt, )) }
| ddecltor= direct_declarator LBRACKET STATIC qs_opt= type_qualifier_list? expr= assignment_expression RBRACKET
    { DDecl_array }
| ddecltor= direct_declarator LBRACKET qs= type_qualifier_list STATIC expr= assignment_expression RBRACKET
    { DDecl_array }
| ddecltor= direct_declarator LBRACKET qs_opt= type_qualifier_list? STAR RBRACKET
    { DDecl_array }
| ddecltor= direct_declarator LPAREN parameter_type_list RPAREN
    { DDecl_array }
(* TODO | direct_declarator LPAREN identifier_list? RPAREN *)

pointer:
| STAR type_qualifier_list?
| STAR type_qualifier_list? pointer
    { failwith "TODO" }

type_qualifier_list:
| type_qualifier
| type_qualifier_list type_qualifier
    { failwith "TODO" }

parameter_type_list:
| parameter_list
| parameter_list COMMA ELLIPSIS
    { failwith "TODO" }

parameter_list:
| parameter_declaration
| parameter_list COMMA parameter_declaration
    { failwith "TODO" }

parameter_declaration:
| declaration_specifiers declarator
| declaration_specifiers abstract_declarator?
    { failwith "TODO" }

(* TODO
identifier_list:
| identifier
| identifier_list COMMA identifier
    { failwith "TODO" }
*)


(* §6.7.7 Type names *)
type_name:
| specs_qs= specifier_qualifier_list abs_declr= abstract_declarator?
    { failwith "TODO" } (* (fst specqual, JUSTBASE) *)
                        (* (fst specqual, typ) *)

abstract_declarator:
| ptr= pointer
    { failwith "TODO" }
| ptr= pointer? dabs_declr= direct_abstract_declarator
    { failwith "TODO" }

 (* NOTE: this rule is split to avoid a conflict *)
direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN

(* direct_abstract_declarator? LBRACKET type_qualifier_list? assignment_expression? RBRACKET *)
| direct_abstract_declarator LBRACKET type_qualifier_list assignment_expression RBRACKET
| direct_abstract_declarator LBRACKET type_qualifier_list RBRACKET
| direct_abstract_declarator LBRACKET assignment_expression RBRACKET
| direct_abstract_declarator LBRACKET RBRACKET
| LBRACKET type_qualifier_list assignment_expression RBRACKET
| LBRACKET assignment_expression RBRACKET
| LBRACKET type_qualifier_list RBRACKET
| LBRACKET RBRACKET
(* direct_abstract_declarator? LBRACKET STATIC type_qualifier_list? assignment_expression RBRACKET *)
| direct_abstract_declarator LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET
| LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET
| direct_abstract_declarator LBRACKET STATIC assignment_expression RBRACKET
| LBRACKET STATIC assignment_expression RBRACKET
(* direct_abstract_declarator? LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET *)
| direct_abstract_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET
| LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET
(* direct_abstract_declarator? LBRACKET STAR RBRACKET *)
| direct_abstract_declarator LBRACKET STAR RBRACKET
| LBRACKET STAR RBRACKET
(* direct_abstract_declarator? LPAREN parameter_type_list? RPAREN *)
| direct_abstract_declarator LPAREN parameter_type_list? RPAREN
| LPAREN parameter_type_list? RPAREN
    { failwith "TODO" }

(*
TODO

direct_abstract_declarator:
| LPAREN typ = abstract_declarator RPAREN
    { typ }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list expr = assignment_expression RBRACK
    { ARRAY (typ, cvspec, [], Some (fst expr)) }
| LBRACK cvspec = type_qualifier_list expr = assignment_expression RBRACK
    { ARRAY (JUSTBASE, cvspec, [], Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK expr = assignment_expression RBRACK
    { ARRAY (typ, [], [], Some (fst expr)) }
| LBRACK expr = assignment_expression RBRACK
    { ARRAY (JUSTBASE, [], [], Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list RBRACK
    { ARRAY (typ, cvspec, [], None) }
| LBRACK cvspec = type_qualifier_list RBRACK
    { ARRAY (JUSTBASE, cvspec, [], None) }
| typ = direct_abstract_declarator LBRACK RBRACK
    { ARRAY (typ, [], [], None) }
| LBRACK RBRACK
    { ARRAY (JUSTBASE, [], [], None) }
(*| direct_abstract_declarator? LBRACK STAR RBRACK*)
(*| direct_abstract_declarator? LBRACK ... STATIC ... RBRACK*)
| typ = direct_abstract_declarator LPAREN params = parameter_type_list RPAREN
    { PROTO (typ, params) }
| LPAREN params = parameter_type_list RPAREN
    { PROTO (JUSTBASE, params) }
| typ = direct_abstract_declarator LPAREN RPAREN
    { PROTO (typ, ([], false)) }
| LPAREN RPAREN
    { PROTO (JUSTBASE, ([], false)) }
*)


(* §6.7.8 Type definitions
  
  NOTE: This is dealt with during the pre parsing and appear
        here as the token TYPEDEF_NAME2
*)


(* §6.7.9 Initialization *)
initializer_:
| expr= assignment_expression
    { Init_expr expr }
| LBRACE inits= initializer_list RBRACE
| LBRACE inits= initializer_list COMMA RBRACE
    { Init_list (List.rev inits) }

initializer_list: (* NOTE: the list is in reverse *)
| design= designation? init= initializer_
    { failwith "TODO" } (* [(design, init)] *)
| inits= initializer_list COMMA design_opt= designation? init= initializer_
    { failwith "TODO" } (* (design, init)::initq *)

designation:
| design= designator_list EQ
    { List.rev design }

designator_list: (* NOTE: the list is in reverse *)
| design= designator
    { [design] }
| designs= designator_list design= designator
    { design::designs }

designator:
| LBRACKET expr= constant_expression RBRACKET
    { Desig_array expr }
| DOT id= OTHER_NAME
    { Desig_member id }


(* §6.7.10 Static assertions *)
static_assert_declaration:
| STATIC_ASSERT LPAREN expr= constant_expression COMMA str= STRING_LITERAL RPAREN SEMICOLON
    { failwith "TODO" }


(* §6.8 Statements and blocks *)
statement_dangerous:
| stmt= labeled_statement(statement_dangerous)
| stmt= compound_statement
| stmt= expression_statement
| stmt= selection_statement_dangerous
| stmt= iteration_statement(statement_dangerous)
| stmt= jump_statement
    { stmt }

statement_safe:
| stmt= labeled_statement(statement_safe)
| stmt= compound_statement
| stmt= expression_statement
| stmt= selection_statement_safe
| stmt= iteration_statement(statement_safe)
| stmt= jump_statement
    { stmt }


(* §6.8.1 Labeled statements *)
labeled_statement(last_statement):
| id= OTHER_NAME COLON stmt= last_statement
    { Slabel (id, stmt) }
| CASE expr= constant_expression COLON stmt= last_statement
    { Scase (expr, stmt) }
| DEFAULT COLON stmt= last_statement
    { Sdefault stmt }


(* §6.8.2 Compound statement *)
compound_statement:
| LBRACE bis_opt= block_item_list? RBRACE
    { Sblock (option [] List.rev bis_opt) }

block_item_list: (* NOTE: the list is in reverse *)
| stmt= block_item
    { [stmt] }
| stmts= block_item_list stmt= block_item
    { stmt::stmts }

block_item:
| decl= declaration
    { Sdecl decl }
| stmt= statement_dangerous
    { stmt }


(* §6.8.3 Expression and null statements *)
expression_statement:
| expr_opt= expression? SEMICOLON
    { option Snull (fun z -> Sexpr z) expr_opt }


(* §6.8.4 Selection statements *)
selection_statement_dangerous:
| IF LPAREN expr= expression RPAREN stmt= statement_dangerous
    { Sif (expr, stmt, None) }
| IF LPAREN expr= expression RPAREN stmt1= statement_safe ELSE stmt2= statement_dangerous
    { Sif (expr, stmt1, Some stmt2) }
| SWITCH LPAREN expr= expression RPAREN stmt= statement_dangerous
    { Sswitch (expr, stmt) }

selection_statement_safe:
| IF LPAREN expr= expression RPAREN stmt1= statement_safe ELSE stmt2= statement_safe
    { Sif (expr, stmt1, Some stmt2) }
| SWITCH LPAREN expr= expression RPAREN stmt= statement_safe
    { Sswitch (expr, stmt) }


(* §6.8.5 Iteration statements *)
iteration_statement(last_statement):
| WHILE LPAREN expr= expression RPAREN stmt= last_statement
    { Swhile (expr, stmt) }
| DO stmt= statement_dangerous WHILE LPAREN expr= expression RPAREN SEMICOLON
    { Sdo (expr, stmt) }
| FOR LPAREN expr1_opt= expression? SEMICOLON expr2_opt= expression? SEMICOLON expr3_opt= expression? RPAREN stmt= last_statement
    { Sfor (option None (fun z -> Some (FC_expr z)) expr1_opt, expr2_opt, expr3_opt, stmt) }
| FOR LPAREN decl= declaration expr2_opt= expression? SEMICOLON expr3_opt= expression? RPAREN stmt= last_statement
    { Sfor (Some (FC_decl decl), expr2_opt, expr3_opt, stmt) }


(* §6.8.6 Jump statements *)
jump_statement:
| GOTO id= OTHER_NAME SEMICOLON
    { Sgoto id }
| CONTINUE SEMICOLON
    { Scontinue }
| BREAK SEMICOLON
    { Sbreak }
| RETURN expr_opt= expression? SEMICOLON
    { Sreturn expr_opt }


(* §6.9 External definitions *)
translation_unit:
| def= external_declaration
    { [def] }
| defs = translation_unit def= external_declaration
    { def :: defs }

external_declaration:
| def= function_definition
| def= declaration
    { def }


(* §6.9.1 Function definitions *)
(* TODO: declaration_list (this is old K&R ??) *)
function_definition:
| specs= declaration_specifiers decl= declarator stmt= compound_statement
    { failwith "TODO" (* FDef (specs, decl, stmt) *) }




(* ========= *)















(*



%type<Cabs0.expression0 * Cabs0.cabsloc> primary_expression (* atomic_operation *) postfix_expression
  unary_expression cast_expression multiplicative_expression additive_expression
  shift_expression relational_expression equality_expression AND_expression
  exclusive_OR_expression inclusive_OR_expression logical_AND_expression
  logical_OR_expression conditional_expression assignment_expression
  constant_expression expression
%type<Cabs0.unary_operator * Cabs0.cabsloc> unary_operator
%type<Cabs0.binary_operator> assignment_operator
%type<Cabs0.expression0 list (* Reverse order *)> argument_expression_list
%type<Cabs0.definition> declaration
%type<Cabs0.spec_elem list * Cabs0.cabsloc> declaration_specifiers
%type<Cabs0.init_name list (* Reverse order *)> init_declarator_list
%type<Cabs0.init_name> init_declarator
%type<Cabs0.storage * Cabs0.cabsloc> storage_class_specifier
%type<Cabs0.typeSpecifier * Cabs0.cabsloc> type_specifier struct_or_union_specifier enum_specifier
(* %type<Cabs0.typeSpecifier * Cabs0.cabsloc> atomic_type_specifier *)
%type<(Cabs0.atom option -> (Cabs0.field_group list) option -> attribute list -> typeSpecifier) * Cabs0.cabsloc> struct_or_union
%type<field_group list (* Reverse order *)> struct_declaration_list
%type<field_group> struct_declaration
%type<spec_elem list * Cabs0.cabsloc> specifier_qualifier_list
%type<(name option * Cabs0.expression0 option) list (* Reverse order *)> struct_declarator_list
%type<name option * Cabs0.expression0 option> struct_declarator
%type<(atom * Cabs0.expression0 option * Cabs0.cabsloc) list (* Reverse order *)> enumerator_list
%type<atom * Cabs0.expression0 option * Cabs0.cabsloc> enumerator
%type<atom * Cabs0.cabsloc> enumeration_constant
%type<cvspec * Cabs0.cabsloc> type_qualifier
%type<Cabs0.cabsloc> function_specifier
%type<Cabs0.name> declarator direct_declarator
%type<(Cabs0.decl_type -> Cabs0.decl_type) * Cabs0.cabsloc> pointer
%type<Cabs0.cvspec list (* Reverse order *)> type_qualifier_list
%type<Cabs0.parameter list * bool> parameter_type_list
%type<Cabs0.parameter list (* Reverse order *)> parameter_list
%type<Cabs0.parameter> parameter_declaration
%type<Cabs0.spec_elem list * Cabs0.decl_type> type_name
%type<Cabs0.decl_type> abstract_declarator direct_abstract_declarator
%type<Cabs0.init_expression> c_initializer
%type<(Cabs0.initwhat list * Cabs0.init_expression) list (* Reverse order *)> initializer_list
%type<Cabs0.initwhat list> designation
%type<Cabs0.initwhat list (* Reverse order *)> designator_list
%type<Cabs0.initwhat> designator
%type<Cabs0.statement0> statement_dangerous statement_safe 
  labeled_statement(statement_safe) labeled_statement(statement_dangerous)
  iteration_statement(statement_safe) iteration_statement(statement_dangerous)
  compound_statement
%type<Cabs0.statement0 list (* Reverse order *)> block_item_list
%type<Cabs0.statement0> block_item expression_statement selection_statement_dangerous
  selection_statement_safe jump_statement
%type<Cabs0.definition list (* Reverse order *)> translation_unit
%type<Cabs0.definition> external_declaration function_definition

%type<Cabs0.statement0>par_statement
%type<Cabs0.statement0 list> par_statement_list



%start<Cabs0.definition list> translation_unit_file
*)
