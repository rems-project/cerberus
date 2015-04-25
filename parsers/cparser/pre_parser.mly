%{
  open Pre_parser_aux

  let set_id_type (z,r) t =
    r := t

  let declare_varname (i,_) =
    !declare_varname i

  let declare_typename (i,_) =
    !declare_typename i
%}


(* §6.4.1 keywords *)
%token AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE ENUM EXTERN
  FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN SHORT SIGNED SIZEOF
  STATIC STRUCT SWITCH TYPEDEF UNION UNSIGNED VOID VOLATILE WHILE ALIGNAS
  ALIGNOF ATOMIC BOOL COMPLEX GENERIC (* IMAGINARY *) NORETURN STATIC_ASSERT
  THREAD_LOCAL
  ATOMIC_LPAREN (* this is a hack to solve a grammar ambiguity (see Lexer.mll) *)




(* §6.4.2 Identifiers *)
%token<Cabs.cabs_identifier * Pre_parser_aux.identifier_type ref>
  VAR_NAME TYPEDEF_NAME UNKNOWN_NAME

(* §6.4.4 Constants *)
%token<Cabs.cabs_constant> CONSTANT

(* §6.4.5 String literals *)
%token<Cabs.cabs_string_literal> STRING_LITERAL

(* §6.4.6 Punctuators *)
%token LBRACKET RBRACKET LPAREN RPAREN LBRACE RBRACE DOT MINUS_GT
  PLUS_PLUS MINUS_MINUS AMPERSAND STAR PLUS MINUS TILDE BANG
  SLASH PERCENT LT_LT GT_GT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET PIPE AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON SEMICOLON ELLIPSIS
  EQ STAR_EQ SLASH_EQ PERCENT_EQ PLUS_EQ MINUS_EQ LT_LT_EQ GT_GT_EQ AMPERSAND_EQ CARET_EQ PIPE_EQ
  COMMA (* TODO: HASH HASH_HASH *)
(* TODO(in lexer?)  LT_COLON COLON_GT LT_PERCENT PERCENT_GT PERCENT_COLON PERCENT_COLON_PERCENT_COLON *)

  ASSERT OFFSETOF
(* NON-STD cppmem syntax *)
(* LBRACES PIPES RBRACES *)

%token EOF


(* These precedences declarations solve the conflict in the following declaration :

int f(int (a));

when a is a TYPEDEF_NAME. It is solved by 6.7.5.3 11.
*)
%nonassoc TYPEDEF_NAME
%nonassoc highPrec

%start<unit> translation_unit_file
%%

(* Helpers *)


%inline option(X):
| /* nothing */
    { None }
| x= X
    { Some x }

%inline fst(X):
| x= X
    { fst x }

general_identifier:
| id= VAR_NAME
| id= TYPEDEF_NAME
| id= UNKNOWN_NAME
    { id }

(*
non_type_identifier:
| i = VAR_NAME
| i = UNKNOWN_NAME
    { i }
*)

string_literals_list:
| STRING_LITERAL
| string_literals_list STRING_LITERAL
    {}

push_context:
  (* empty *)%prec highPrec { !push_context () }
pop_context:
  (* empty *) { !pop_context () }
in_context(nt):
  push_context x = nt pop_context { x }

declare_varname(nt):
  i = nt { declare_varname i; i }

declare_typename(nt):
  i = nt { declare_typename i; i }

(* ========================================================================== *)
translation_unit_file: (* NOTE: this is not present in the standard *)
| translation_unit EOF
    {}
| error
    { Parser_errors.fatal_error "%s:%d:%d Error:@ parse error"
        $startpos.Lexing.pos_fname $startpos.Lexing.pos_lnum $startpos.Lexing.pos_bol }


(* Actual grammar *)


(* §6.5.1 Primary expressions *)
primary_expression:
| id= VAR_NAME
    { set_id_type id VarId }
| CONSTANT
| string_literals_list
| LPAREN expression RPAREN
| generic_selection
    {}


(* §6.5.1.1 Generic selection *)
generic_selection:
| GENERIC LPAREN assignment_expression COMMA generic_assoc_list RPAREN
    {}

generic_assoc_list:
| generic_association
| generic_assoc_list COMMA generic_association
    {}

generic_association:
| type_name COLON assignment_expression
| DEFAULT COLON assignment_expression
    {}


(* §6.5.2 Postfix operators *)
postfix_expression:
| primary_expression
| postfix_expression LBRACKET expression RBRACKET
| postfix_expression LPAREN argument_expression_list? RPAREN
    {}
| postfix_expression DOT id= general_identifier
| postfix_expression MINUS_GT id= general_identifier
    { set_id_type id (OtherId "postfix_expression") }
| postfix_expression PLUS_PLUS
| postfix_expression MINUS_MINUS
| LPAREN type_name RPAREN LBRACE initializer_list RBRACE
| LPAREN type_name RPAREN LBRACE initializer_list COMMA RBRACE
(* NOTE: the following are suppose to be part of the C library, but are "special" *)
| ASSERT LPAREN assignment_expression RPAREN
    { }
| OFFSETOF LPAREN type_name COMMA id= general_identifier RPAREN
    { set_id_type id (OtherId "offsetof") }

argument_expression_list:
| assignment_expression
| argument_expression_list COMMA assignment_expression
    {}


(* §6.5.3 Unary operators *)
unary_expression:
| postfix_expression
| PLUS_PLUS unary_expression
| MINUS_MINUS unary_expression
| unary_operator cast_expression
| SIZEOF unary_expression
| SIZEOF LPAREN type_name RPAREN
| ALIGNOF LPAREN type_name RPAREN
    {}

unary_operator:
| AMPERSAND
| STAR
| PLUS
| MINUS
| TILDE
| BANG
    {}


(* §6.5.4 Cast operators *)
cast_expression:
| unary_expression
| LPAREN type_name RPAREN cast_expression
    {}


(* §6.5.5 Multiplicative operators *)
multiplicative_expression:
| cast_expression
| multiplicative_expression STAR cast_expression
| multiplicative_expression SLASH cast_expression
| multiplicative_expression PERCENT cast_expression
    {}


(* §6.5.6 Additive operators *)
additive_expression:
| multiplicative_expression
| additive_expression PLUS multiplicative_expression
| additive_expression MINUS multiplicative_expression
    {}


(* §6.5.7 Bitwise shift operators *)
shift_expression:
| additive_expression
| shift_expression LT_LT additive_expression
| shift_expression GT_GT additive_expression
    {}


(* §6.5.8 Relational operators *)
relational_expression:
| shift_expression
| relational_expression LT shift_expression
| relational_expression GT shift_expression
| relational_expression LT_EQ shift_expression
| relational_expression GT_EQ shift_expression
    {}


(* §6.5.9 Equality operators *)
equality_expression:
| relational_expression
| equality_expression EQ_EQ relational_expression
| equality_expression BANG_EQ relational_expression
    {}


(* §6.5.10 Bitwise AND operator *)
_AND_expression:
| equality_expression
| _AND_expression AMPERSAND equality_expression
    {}


(* §6.5.11 Bitwise exclusive OR operator *)
exclusive_OR_expression:
| _AND_expression
| exclusive_OR_expression CARET _AND_expression
    {}


(* §6.5.12 Bitwise inclusive OR operator *)
inclusive_OR_expression:
| exclusive_OR_expression
| inclusive_OR_expression PIPE exclusive_OR_expression
    {}


(* §6.5.13 Logical AND operator *)
logical_AND_expression:
| inclusive_OR_expression
| logical_AND_expression AMPERSAND_AMPERSAND inclusive_OR_expression
    {}


(* §6.5.14 Logical OR operator *)
logical_OR_expression:
| logical_AND_expression
| logical_OR_expression PIPE_PIPE logical_AND_expression
    {}


(* §6.5.15 Conditional operator *)
conditional_expression:
| logical_OR_expression
| logical_OR_expression QUESTION expression COLON conditional_expression
    {}


(* §6.5.16 Assignment operators *)
assignment_expression:
| conditional_expression
| unary_expression assignment_operator assignment_expression
    {}

assignment_operator:
| EQ
| STAR_EQ
| SLASH_EQ
| PERCENT_EQ
| PLUS_EQ
| MINUS_EQ
| LT_LT_EQ
| GT_GT_EQ
| AMPERSAND_EQ
| CARET_EQ
| PIPE_EQ
    {}


(* §6.5.17 Comma operator *)
expression:
| assignment_expression
| expression COMMA assignment_expression
    {}


(* §6.6 Constant expressions *)
constant_expression:
| conditional_expression
    {}


(* §6.7 Declarations *)
(* NOTE: we slightly defer from the STD here, typedef are dealt with
         separately (see the second production) *)
(* BEGIN TODO: documentation *)
declaration:
| declaration_specifiers init_declarator_list? SEMICOLON
| declaration_specifiers_typedef typedef_declarator_list? SEMICOLON
| static_assert_declaration
    {}

declaration_specifiers:
| declaration_specifiers_no_type? id= TYPEDEF_NAME declaration_specifiers_no_type?
    { set_id_type id TypedefId }
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
    {}

declaration_specifiers_no_type:
| storage_class_specifier_no_typedef declaration_specifiers_no_type?
| type_qualifier declaration_specifiers_no_type?
| function_specifier declaration_specifiers_no_type?
| alignment_specifier declaration_specifiers_no_type?
    {}

declaration_specifiers_no_typedef_name:
| storage_class_specifier_no_typedef declaration_specifiers_no_typedef_name?
| type_qualifier declaration_specifiers_no_typedef_name?
| function_specifier declaration_specifiers_no_typedef_name?
| alignment_specifier declaration_specifiers_no_typedef_name?
| type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
    {}

declaration_specifiers_typedef:
| declaration_specifiers_no_type? TYPEDEF declaration_specifiers_no_type? i = TYPEDEF_NAME declaration_specifiers_no_type?
| declaration_specifiers_no_type? i = TYPEDEF_NAME declaration_specifiers_no_type? TYPEDEF declaration_specifiers_no_type?
    { set_id_type i TypedefId }
| declaration_specifiers_no_type? TYPEDEF declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name? TYPEDEF declaration_specifiers_no_typedef_name?
    {}

init_declarator_list:
| init_declarator
| init_declarator_list COMMA init_declarator
    {}

init_declarator:
| declare_varname(fst(declarator))
| declare_varname(fst(declarator)) EQ initializer_
    { }

typedef_declarator_list:
| typedef_declarator
| typedef_declarator_list COMMA typedef_declarator
    {}

typedef_declarator:
| declare_typename(fst(declarator))
    { }

storage_class_specifier_no_typedef:
| EXTERN
| STATIC
| THREAD_LOCAL
| AUTO
| REGISTER
    {}
(* END TODO: documentation *)





(* §6.7.2 Type specifiers *)
(* NOTE: this defers from the STD by omitting the typedef names production *)
type_specifier_no_typedef_name:
| VOID
| CHAR
| SHORT
| INT
| LONG
| FLOAT
| DOUBLE
| SIGNED
| UNSIGNED
| BOOL
| COMPLEX
| atomic_type_specifier
| struct_or_union_specifier
| enum_specifier
    {}


(* §6.7.2.1 Structure and union specifiers *)
struct_or_union_specifier:
| struct_or_union LBRACE struct_declaration_list RBRACE
    {}
| struct_or_union id= general_identifier LBRACE struct_declaration_list RBRACE
| struct_or_union id= general_identifier
    { set_id_type id (OtherId "struct_or_union") }

struct_or_union:
| STRUCT
| UNION
    {}

struct_declaration_list:
| struct_declaration
| struct_declaration_list struct_declaration
    {}

struct_declaration:
| specifier_qualifier_list struct_declarator_list? SEMICOLON
| static_assert_declaration
    {}

(* TODO: documentation (differ from STD) *)
specifier_qualifier_list:
| type_qualifier_list? id= TYPEDEF_NAME type_qualifier_list?
    { set_id_type id TypedefId }
| type_qualifier_list? type_specifier_no_typedef_name specifier_qualifier_list_no_typedef_name?
    {}

(* TODO: documentation (differ from STD) *)
specifier_qualifier_list_no_typedef_name:
| type_specifier_no_typedef_name specifier_qualifier_list_no_typedef_name?
| type_qualifier specifier_qualifier_list_no_typedef_name?
    {}

struct_declarator_list:
| struct_declarator
| struct_declarator_list COMMA struct_declarator
    {}

struct_declarator:
| declarator
| declarator? COLON constant_expression
    {}


(* §6.7.2.2 Enumeration specifiers *)
(* TODO: documentation (differ from STD) *)
enum_specifier:
| ENUM LBRACE enumerator_list RBRACE
| ENUM LBRACE enumerator_list COMMA RBRACE
    {}
| ENUM id= general_identifier LBRACE enumerator_list RBRACE
| ENUM id= general_identifier LBRACE enumerator_list COMMA RBRACE
| ENUM id= general_identifier
    { set_id_type id (OtherId "enum_specifier") }

(* TODO: documentation (differ from STD) *)
enumerator_list:
| declare_varname(enumerator)
| enumerator_list COMMA declare_varname(enumerator)
    {}

(* TODO: documentation (differ from STD) *)
enumerator:
| id= enumeration_constant
| id= enumeration_constant EQ constant_expression
    { id }

(* TODO: documentation (differ from STD) *)
enumeration_constant:
| id= general_identifier
    { set_id_type id VarId; id }


(* §6.7.2.4 Atomic type specifiers *)
atomic_type_specifier:
| ATOMIC_LPAREN type_name RPAREN
    {}


(* §6.7.3 Type qualifiers *)
type_qualifier:
| CONST
| RESTRICT
| VOLATILE
| ATOMIC
    {}


function_specifier:
| INLINE
| NORETURN
    {}


(* §6.7.5 Alignment specifier *)
alignment_specifier:
| ALIGNAS LPAREN type_name RPAREN
| ALIGNAS LPAREN constant_expression RPAREN
    {}


(* §6.7.6 Declarators *)
declarator:
| pointer? x= direct_declarator
    { x }

direct_declarator:
| id= general_identifier
    { set_id_type id VarId; (id, None) }
| LPAREN x= declarator RPAREN
| x= direct_declarator LBRACKET type_qualifier_list? assignment_expression? RBRACKET
| x= direct_declarator LBRACKET STATIC type_qualifier_list? assignment_expression RBRACKET
| x= direct_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET
| x= direct_declarator LBRACKET type_qualifier_list? STAR RBRACKET
    { x }
| x= direct_declarator LPAREN l=in_context(parameter_type_list) RPAREN
    { match snd x with
      | None -> (fst x, Some l)
      | Some _ -> x }
(* TODO(check) : K&R *)
| x= direct_declarator LPAREN RPAREN
    { match snd x with
      | None -> (fst x, Some [])
      | Some _ -> x }
(* TODO
| x = direct_declarator LPAREN l = identifier_list RPAREN
    { match snd x with
      | None -> (fst x, Some [])
      | Some _ -> $syntaxerror }
*)

pointer:
| STAR type_qualifier_list?
| STAR type_qualifier_list? pointer
    {}

type_qualifier_list:
| type_qualifier
| type_qualifier_list type_qualifier
    {}

parameter_type_list:
| l= parameter_list
| l= parameter_list COMMA ELLIPSIS
    { l }

parameter_list:
| i= parameter_declaration
    { [i] }
| l= parameter_list COMMA i= parameter_declaration
    { i::l }

(* TODO: documentation (differ from STD) *)
parameter_declaration:
| declaration_specifiers id= declare_varname(fst(declarator))
    { Some id }
| declaration_specifiers abstract_declarator?
    { None }

(* TODO : K&R *)
(*
identifier_list: (* 6.7.5.3 3 indicates that this case shall only appears in function definitions. *)
                 (* 6.9.1 6 indicates that there can't be TYPEDEF_NAME here. *)
| i = non_type_identifier
| identifier_list COMMA_ i = non_type_identifier
    { set_id_type i VarId }
*)


(* §6.7.7 Type names *)
type_name:
| specifier_qualifier_list abstract_declarator?
    {}

abstract_declarator:
| pointer
| pointer? direct_abstract_declarator
    {}

(* TODO: documentation (differ from STD) *)
direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN
| direct_abstract_declarator? LBRACKET type_qualifier_list? assignment_expression? RBRACKET
| direct_abstract_declarator? LBRACKET STATIC type_qualifier_list? assignment_expression RBRACKET
| direct_abstract_declarator? LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET
| direct_abstract_declarator? LBRACKET STAR RBRACKET
| direct_abstract_declarator? LPAREN in_context(parameter_type_list?) RPAREN
    {}


(* §6.7.9 Initialization *)
initializer_:
| assignment_expression
| LBRACE initializer_list RBRACE
| LBRACE initializer_list COMMA RBRACE
    {}

initializer_list:
| designation? initializer_
| initializer_list COMMA designation? initializer_
    {}

designation:
| designator_list EQ
    {}

designator_list:
| designator
| designator_list designator
    {}

designator:
| LBRACKET constant_expression RBRACKET
    {}
| DOT id= general_identifier
    { set_id_type id (OtherId "designator") }


(* §6.7.10 Static assertions *)
(* TODO: this doesn't allow list of string literals (to be concatenated) *)
static_assert_declaration:
| STATIC_ASSERT LPAREN constant_expression COMMA STRING_LITERAL RPAREN SEMICOLON
    {}


(* §6.8 Statements and blocks *)
(* TODO: documentation (differ from STD) *)
statement_dangerous:
| labeled_statement(statement_dangerous)
| in_context(compound_statement)
| expression_statement
| selection_statement_dangerous
| iteration_statement(statement_dangerous)
| jump_statement
    {}

statement_safe:
| labeled_statement(statement_safe)
| in_context(compound_statement)
| expression_statement
| selection_statement_safe
| iteration_statement(statement_safe)
| jump_statement
    {}


(* §6.8.1 Labeled statements *)
labeled_statement(last_statement):
| id= general_identifier COLON last_statement
    { set_id_type id (OtherId "labeled_statement") }
| CASE constant_expression COLON last_statement
| DEFAULT COLON last_statement
    {}


(* §6.8.2 Compound statement *)
compound_statement:
| LBRACE block_item_list? RBRACE
(* NON-STD cppmem syntax *)
(*
| LBRACES separated_nonempty_list(PIPES, compound_statement) RBRACES
*)
    {}

block_item_list:
| block_item_list? block_item
    {}

block_item:
| declaration
| statement_dangerous
    {}


(* §6.8.3 Expression and null statements *)
expression_statement:
| expression? SEMICOLON
    {}


(* §6.8.4 Selection statements *)
selection_statement_dangerous:
| IF LPAREN expression RPAREN statement_dangerous
| IF LPAREN expression RPAREN statement_safe ELSE statement_dangerous
| SWITCH LPAREN expression RPAREN statement_dangerous
    {}

selection_statement_safe:
| IF LPAREN expression RPAREN statement_safe ELSE statement_safe
| SWITCH LPAREN expression RPAREN statement_safe
    {}


(* §6.8.5 Iteration statements *)
iteration_statement(last_statement):
| WHILE LPAREN expression RPAREN last_statement
| DO statement_dangerous WHILE LPAREN expression RPAREN SEMICOLON
| FOR LPAREN expression? SEMICOLON expression? SEMICOLON expression? RPAREN last_statement
| FOR LPAREN declaration expression? SEMICOLON expression? RPAREN last_statement
    {}


(* §6.8.6 Jump statements *)
jump_statement:
| GOTO id= general_identifier SEMICOLON
    { set_id_type id (OtherId "jump_statement") }
| CONTINUE SEMICOLON
| BREAK SEMICOLON
| RETURN expression? SEMICOLON
    {}


(* §6.9 External definitions *)
translation_unit:
| external_declaration
| translation_unit external_declaration
    {}

external_declaration:
| function_definition
| declaration
    {}


(* §6.9.1 Function definitions *)
(* TODO: check+documentation (differ from STD) *)
function_definition_begin:
| declaration_specifiers pointer? x= direct_declarator
    { match x with
      | (_, None) -> $syntaxerror
      | (i, Some l) ->
	declare_varname i;
	!push_context ();
	List.iter (fun x ->
	  match x with
	    | None -> ()
	    | Some i -> declare_varname i
	  ) l;
	declare_varname (CabsIdentifier (Location_ocaml.unknown, "__func__"), ())
    }

(* TODO: declaration_list (this is old K&R ??) *)
function_definition:
| function_definition_begin (* declaration_list? *) compound_statement
    { !pop_context () }
