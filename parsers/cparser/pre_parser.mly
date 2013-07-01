%{
  open Pre_parser_aux

  let set_id_type (_,r,_) t =
    r := t

  let declare_varname (i,_,_) =
    !declare_varname i

  let declare_typename (i,_,_) =
    !declare_typename i
%}

%token<string * Pre_parser_aux.identifier_type ref * Cabs0.cabsloc> 
  VAR_NAME TYPEDEF_NAME UNKNOWN_NAME
%token<Cabs0.constant * Cabs0.cabsloc> CONSTANT
%token<string * Cabs0.cabsloc> STRING_LITERAL

%token<Cabs0.cabsloc> SIZEOF ALIGNOF PTR INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ NEQ LT GT
  ANDAND BARBAR PLUS MINUS STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION
  COLON AND MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN SUB_ASSIGN LEFT_ASSIGN
  RIGHT_ASSIGN AND_ASSIGN XOR_ASSIGN OR_ASSIGN LPAREN RPAREN LBRACK RBRACK 
  LBRACE RBRACE DOT COMMA SEMICOLON ELLIPSIS TYPEDEF EXTERN STATIC RESTRICT
  AUTO REGISTER INLINE CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE BOOL
  CONST VOLATILE VOID STRUCT UNION ENUM CASE DEFAULT IF ELSE SWITCH WHILE DO 
  FOR GOTO CONTINUE BREAK RETURN BUILTIN_VA_ARG OFFSETOF STATIC_ASSERT

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
| x = X
    { Some x }

%inline fst(X):
| x = X
    { fst x }

general_identifier:
| i = VAR_NAME
| i = TYPEDEF_NAME
| i = UNKNOWN_NAME
    { i }

non_type_identifier:
| i = VAR_NAME
| i = UNKNOWN_NAME
    { i }

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

(* Actual grammar *)

primary_expression:
| i = VAR_NAME
    { set_id_type i VarId }
| CONSTANT
| string_literals_list
| LPAREN expression RPAREN
    {}

postfix_expression:
| primary_expression
| postfix_expression LBRACK expression RBRACK
| postfix_expression LPAREN argument_expression_list? RPAREN
| BUILTIN_VA_ARG LPAREN assignment_expression COMMA type_name RPAREN
    {}
| postfix_expression DOT i = general_identifier
| postfix_expression PTR i = general_identifier
    { set_id_type i OtherId }
| postfix_expression INC
| postfix_expression DEC
| LPAREN type_name RPAREN LBRACE initializer_list COMMA? RBRACE
    {}

argument_expression_list:
| assignment_expression
| argument_expression_list COMMA assignment_expression
    {}

unary_expression:
| postfix_expression
| INC unary_expression
| DEC unary_expression
| unary_operator cast_expression
| SIZEOF unary_expression
| SIZEOF LPAREN type_name RPAREN
| ALIGNOF LPAREN type_name RPAREN
    {}
(* TODO: in GCC the second argument may be more complexe than what we allow for now *)
| OFFSETOF LPAREN type_name COMMA i = general_identifier RPAREN
    { set_id_type i OtherId }


unary_operator:
| AND
| STAR
| PLUS
| MINUS
| TILDE
| BANG
    {}

cast_expression:
| unary_expression
| LPAREN type_name RPAREN cast_expression
    {}

multiplicative_expression:
| cast_expression
| multiplicative_expression STAR cast_expression
| multiplicative_expression SLASH cast_expression
| multiplicative_expression PERCENT cast_expression
    {}

additive_expression:
| multiplicative_expression
| additive_expression PLUS multiplicative_expression
| additive_expression MINUS multiplicative_expression
    {}

shift_expression:
| additive_expression
| shift_expression LEFT additive_expression
| shift_expression RIGHT additive_expression
    {}

relational_expression:
| shift_expression
| relational_expression LT shift_expression
| relational_expression GT shift_expression
| relational_expression LEQ shift_expression
| relational_expression GEQ shift_expression
    {}

equality_expression:
| relational_expression
| equality_expression EQEQ relational_expression
| equality_expression NEQ relational_expression
    {}

and_expression:
| equality_expression
| and_expression AND equality_expression
    {}

exclusive_or_expression:
| and_expression
| exclusive_or_expression HAT and_expression
    {}

inclusive_or_expression:
| exclusive_or_expression
| inclusive_or_expression BAR exclusive_or_expression
    {}

logical_and_expression:
| inclusive_or_expression
| logical_and_expression ANDAND inclusive_or_expression
    {}

logical_or_expression:
| logical_and_expression
| logical_or_expression BARBAR logical_and_expression
    {}

conditional_expression:
| logical_or_expression
| logical_or_expression QUESTION expression COLON conditional_expression
    {}

assignment_expression:
| conditional_expression
| unary_expression assignment_operator assignment_expression
    {}

assignment_operator:
| EQ
| MUL_ASSIGN
| DIV_ASSIGN
| MOD_ASSIGN
| ADD_ASSIGN
| SUB_ASSIGN
| LEFT_ASSIGN
| RIGHT_ASSIGN
| AND_ASSIGN
| XOR_ASSIGN
| OR_ASSIGN
    {}

expression:
| assignment_expression
| expression COMMA assignment_expression
    {}

constant_expression:
| conditional_expression
    {}

declaration:
| declaration_specifiers init_declarator_list? SEMICOLON
| declaration_specifiers_typedef typedef_declarator_list? SEMICOLON
(*
| static_assert_declaration
*)
    {}

declaration_specifiers_no_type:
| storage_class_specifier_no_typedef declaration_specifiers_no_type?
| type_qualifier declaration_specifiers_no_type?
| function_specifier declaration_specifiers_no_type?
    {}

declaration_specifiers_no_typedef_name:
| storage_class_specifier_no_typedef declaration_specifiers_no_typedef_name?
| type_qualifier declaration_specifiers_no_typedef_name?
| function_specifier declaration_specifiers_no_typedef_name?
| type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
    {}

declaration_specifiers:
| declaration_specifiers_no_type? i = TYPEDEF_NAME declaration_specifiers_no_type?
    { set_id_type i TypedefId }
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
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
| declare_varname(fst(declarator)) EQ c_initializer
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
| AUTO
| REGISTER
    {}

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
| struct_or_union_specifier
| enum_specifier
    {}

struct_or_union_specifier:
| struct_or_union LBRACE struct_declaration_list RBRACE
    {}
| struct_or_union i = general_identifier LBRACE struct_declaration_list RBRACE
| struct_or_union i = general_identifier
    { set_id_type i OtherId }

struct_or_union:
| STRUCT
| UNION
    {}

struct_declaration_list:
| struct_declaration_list? struct_declaration
    {}

struct_declaration:
| specifier_qualifier_list struct_declarator_list? SEMICOLON
(*
| static_assert_declaration
*)
    {}

specifier_qualifier_list:
| type_qualifier_list? i = TYPEDEF_NAME type_qualifier_list?
    { set_id_type i TypedefId }
| type_qualifier_list? type_specifier_no_typedef_name specifier_qualifier_list_no_typedef_name?
    {}

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

enum_specifier:
| ENUM LBRACE enumerator_list COMMA? RBRACE
    {}
| ENUM i = general_identifier LBRACE enumerator_list COMMA? RBRACE
| ENUM i = general_identifier
    { set_id_type i OtherId }

enumerator_list:
| declare_varname(enumerator)
| enumerator_list COMMA declare_varname(enumerator)
    {}

enumerator:
| i = enumeration_constant
| i = enumeration_constant EQ constant_expression
    { i }

enumeration_constant:
| i = general_identifier
    { set_id_type i VarId; i }

type_qualifier:
| CONST
| RESTRICT
| VOLATILE
    {}

function_specifier:
| INLINE
    {}

declarator:
| pointer? x = direct_declarator
    { x }

direct_declarator:
| i = general_identifier
    { set_id_type i VarId; (i, None) }
| LPAREN x = declarator RPAREN
| x = direct_declarator LBRACK type_qualifier_list? assignment_expression? RBRACK
(*| x = direct_declarator LBRACK STATIC type_qualifier_list? assignment_expression RBRACK
| x = direct_declarator LBRACK type_qualifier_list STATIC assignment_expression RBRACK
| x = direct_declarator LBRACK type_qualifier_list? STAR RBRACK*)
    { x }
| x = direct_declarator LPAREN l=in_context(parameter_type_list) RPAREN
    { match snd x with
      | None -> (fst x, Some l)
      | Some _ -> x }
(* TODO : K&R *)
| x = direct_declarator LPAREN RPAREN
    { match snd x with
      | None -> (fst x, Some [])
      | Some _ -> x }
(*| x = direct_declarator LPAREN l = identifier_list RPAREN
    { match snd x with
      | None -> (fst x, Some [])
      | Some _ -> $syntaxerror }*)

pointer:
| STAR type_qualifier_list?
| STAR type_qualifier_list? pointer
    {}

type_qualifier_list:
| type_qualifier_list? type_qualifier
    {}

parameter_type_list:
| l=parameter_list
| l=parameter_list COMMA ELLIPSIS
    { l }

parameter_list:
| i=parameter_declaration
    { [i] }
| l=parameter_list COMMA i=parameter_declaration
    { i::l }

parameter_declaration:
| declaration_specifiers id=declare_varname(fst(declarator))
    { Some id }
| declaration_specifiers abstract_declarator?
    { None }

(* TODO : K&R *)
(*
identifier_list: (* 6.7.5.3 3 indicates that this case shall only appears in function definitions. *)
                 (* 6.9.1 6 indicates that there can't be TYPEDEF_NAME here. *)
| i = non_type_identifier
| identifier_list COMMA i = non_type_identifier
    { set_id_type i VarId }
*)

type_name:
| specifier_qualifier_list abstract_declarator?
    {}

abstract_declarator:
| pointer
| pointer? direct_abstract_declarator
    {}

direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN
| direct_abstract_declarator? LBRACK type_qualifier_list? assignment_expression? RBRACK
(*| direct_abstract_declarator? LBRACK STATIC type_qualifier_list? assignment_expression RBRACK
| direct_abstract_declarator? LBRACK type_qualifier_list STATIC assignment_expression RBRACK
| direct_abstract_declarator? LBRACK STAR RBRACK*)
| direct_abstract_declarator? LPAREN in_context(parameter_type_list?) RPAREN
    {}

c_initializer:
| assignment_expression
| LBRACE initializer_list COMMA? RBRACE
    {}

initializer_list:
| designation? c_initializer
| initializer_list COMMA designation? c_initializer
    {}

designation:
| designator_list EQ
    {}

designator_list:
| designator_list? designator
    {}

designator:
| LBRACK constant_expression RBRACK
    {}
| DOT i = general_identifier
    { set_id_type i OtherId }

(*
static_assert_declaration:
| STATIC_ASSERT LPAREN constant_expression COMMA string_literal RPAREN SEMICOLON
    {}
*)


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

labeled_statement(last_statement):
| i = general_identifier COLON last_statement
    { set_id_type i OtherId }
| CASE constant_expression COLON last_statement
| DEFAULT COLON last_statement
    {}

compound_statement:
| LBRACE block_item_list? RBRACE
    {}

block_item_list:
| block_item_list? block_item
    {}

block_item:
| declaration
| statement_dangerous
    {}

expression_statement:
| expression? SEMICOLON
    {}

selection_statement_dangerous:
| IF LPAREN expression RPAREN statement_dangerous
| IF LPAREN expression RPAREN statement_safe ELSE statement_dangerous
| SWITCH LPAREN expression RPAREN statement_dangerous
    {}

selection_statement_safe:
| IF LPAREN expression RPAREN statement_safe ELSE statement_safe
| SWITCH LPAREN expression RPAREN statement_safe
    {}

iteration_statement(last_statement):
| WHILE LPAREN expression RPAREN last_statement
| DO statement_dangerous WHILE LPAREN expression RPAREN SEMICOLON
| FOR LPAREN expression? SEMICOLON expression? SEMICOLON expression? RPAREN last_statement
| FOR LPAREN declaration expression? SEMICOLON expression? RPAREN last_statement
    {}

jump_statement:
| GOTO i = general_identifier SEMICOLON
    { set_id_type i OtherId }
| CONTINUE SEMICOLON
| BREAK SEMICOLON
| RETURN expression? SEMICOLON
    {}

translation_unit_file:
| translation_unit EOF
    {}
| error
    { Parser_errors.fatal_error "%s:%d:%d Error:@ parse error"
        $endpos.Lexing.pos_fname $endpos.Lexing.pos_lnum $endpos.Lexing.pos_cnum }

translation_unit:
| external_declaration
| translation_unit external_declaration
    {}

external_declaration:
| function_definition
| declaration
    {}

function_definition_begin:
| declaration_specifiers pointer? x=direct_declarator
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
	declare_varname ("__func__", (), ())
    }

function_definition:
| function_definition_begin declaration_list? compound_statement
    { !pop_context () }

declaration_list:
| declaration_list? declaration
    {}
