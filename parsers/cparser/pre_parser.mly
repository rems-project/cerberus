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
%token<Cabs0.constant0 * Cabs0.cabsloc> CONSTANT_
%token<string * Cabs0.cabsloc> STRING_LITERAL

%token<Cabs0.cabsloc> SIZEOF ALIGNOF_ PTR_ INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ_ NEQ LT_ GT_
  ANDAND BARBAR PLUS_ MINUS_ STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION_
  COLON AND_ MUL_ASSIGN_ DIV_ASSIGN_ MOD_ASSIGN_ ADD_ASSIGN_ SUB_ASSIGN_ LEFT_ASSIGN
  RIGHT_ASSIGN AND_ASSIGN XOR_ASSIGN_ OR_ASSIGN LPAREN RPAREN LBRACK RBRACK 
  LBRACE RBRACE DOT COMMA_ SEMICOLON ELLIPSIS TYPEDEF_ EXTERN_ STATIC_ RESTRICT
  AUTO_ THREAD_LOCAL_ ATOMIC REGISTER_ INLINE CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE BOOL
  CONST VOLATILE VOID STRUCT UNION ENUM CASE_ DEFAULT_ IF ELSE SWITCH_ WHILE_ DO 
  FOR_ GOTO_ CONTINUE_ BREAK_ RETURN_ BUILTIN_VA_ARG_ OFFSETOF_ STATIC_ASSERT
  LBRACES BARES RBRACES

%token<Cabs0.cabsloc> C11_ATOMIC_INIT_ C11_ATOMIC_STORE_ C11_ATOMIC_LOAD_
  C11_ATOMIC_EXCHANGE_ C11_ATOMIC_COMPARE_EXCHANGE_STRONG_ C11_ATOMIC_COMPARE_EXCHANGE_WEAK_
  C11_ATOMIC_FETCH_KEY_


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
| CONSTANT_
| string_literals_list
| LPAREN expression RPAREN
    {}

(* NOTE: this is not present in the actual C11 syntax *)
atomic_operation:
| C11_ATOMIC_INIT_ LPAREN postfix_expression COMMA_ postfix_expression RPAREN
| C11_ATOMIC_STORE_ LPAREN postfix_expression COMMA_ postfix_expression COMMA_ postfix_expression RPAREN
| C11_ATOMIC_LOAD_ LPAREN postfix_expression COMMA_ postfix_expression RPAREN
| C11_ATOMIC_EXCHANGE_ LPAREN postfix_expression COMMA_ postfix_expression COMMA_ postfix_expression RPAREN
| C11_ATOMIC_COMPARE_EXCHANGE_STRONG_ LPAREN postfix_expression COMMA_ postfix_expression COMMA_
  postfix_expression COMMA_ postfix_expression COMMA_ postfix_expression RPAREN
| C11_ATOMIC_COMPARE_EXCHANGE_WEAK_ LPAREN postfix_expression COMMA_ postfix_expression COMMA_
  postfix_expression COMMA_ postfix_expression COMMA_ postfix_expression RPAREN
    {}

postfix_expression:
| primary_expression
| postfix_expression LBRACK expression RBRACK
(* NOTE: we extend the syntax with builtin C11 atomic operation (the way clang does) *)
| atomic_operation
| postfix_expression LPAREN argument_expression_list? RPAREN
| BUILTIN_VA_ARG_ LPAREN assignment_expression COMMA_ type_name RPAREN
    {}
| postfix_expression DOT i = general_identifier
| postfix_expression PTR_ i = general_identifier
    { set_id_type i OtherId }
| postfix_expression INC
| postfix_expression DEC
| LPAREN type_name RPAREN LBRACE initializer_list COMMA_? RBRACE
    {}

argument_expression_list:
| assignment_expression
| argument_expression_list COMMA_ assignment_expression
    {}

unary_expression:
| postfix_expression
| INC unary_expression
| DEC unary_expression
| unary_operator cast_expression
| SIZEOF unary_expression
| SIZEOF LPAREN type_name RPAREN
| ALIGNOF_ LPAREN type_name RPAREN
    {}
(* TODO: in GCC the second argument may be more complexe than what we allow for now *)
| OFFSETOF_ LPAREN type_name COMMA_ i = general_identifier RPAREN
    { set_id_type i OtherId }


unary_operator:
| AND_
| STAR
| PLUS_
| MINUS_
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
| additive_expression PLUS_ multiplicative_expression
| additive_expression MINUS_ multiplicative_expression
    {}

shift_expression:
| additive_expression
| shift_expression LEFT additive_expression
| shift_expression RIGHT additive_expression
    {}

relational_expression:
| shift_expression
| relational_expression LT_ shift_expression
| relational_expression GT_ shift_expression
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
| and_expression AND_ equality_expression
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
| logical_or_expression QUESTION_ expression COLON conditional_expression
    {}

assignment_expression:
| conditional_expression
| unary_expression assignment_operator assignment_expression
    {}

assignment_operator:
| EQ_
| MUL_ASSIGN_
| DIV_ASSIGN_
| MOD_ASSIGN_
| ADD_ASSIGN_
| SUB_ASSIGN_
| LEFT_ASSIGN
| RIGHT_ASSIGN
| AND_ASSIGN
| XOR_ASSIGN_
| OR_ASSIGN
    {}

expression:
| assignment_expression
| expression COMMA_ assignment_expression
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
| declaration_specifiers_no_type? TYPEDEF_ declaration_specifiers_no_type? i = TYPEDEF_NAME declaration_specifiers_no_type?
| declaration_specifiers_no_type? i = TYPEDEF_NAME declaration_specifiers_no_type? TYPEDEF_ declaration_specifiers_no_type?
    { set_id_type i TypedefId }
| declaration_specifiers_no_type? TYPEDEF_ declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name? TYPEDEF_ declaration_specifiers_no_typedef_name?
    {}

init_declarator_list:
| init_declarator
| init_declarator_list COMMA_ init_declarator
    {}

init_declarator:
| declare_varname(fst(declarator))
| declare_varname(fst(declarator)) EQ_ c_initializer
    { }

typedef_declarator_list:
| typedef_declarator
| typedef_declarator_list COMMA_ typedef_declarator
    {}

typedef_declarator:
| declare_typename(fst(declarator))
    { }

storage_class_specifier_no_typedef:
| EXTERN_
| STATIC_
| AUTO_
| THREAD_LOCAL_
| REGISTER_
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
| atomic_type_specifier
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

atomic_type_specifier:
| ATOMIC LPAREN type_name RPAREN
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
| struct_declarator_list COMMA_ struct_declarator
    {}

struct_declarator:
| declarator
| declarator? COLON constant_expression
    {}

enum_specifier:
| ENUM LBRACE enumerator_list COMMA_? RBRACE
    {}
| ENUM i = general_identifier LBRACE enumerator_list COMMA_? RBRACE
| ENUM i = general_identifier
    { set_id_type i OtherId }

enumerator_list:
| declare_varname(enumerator)
| enumerator_list COMMA_ declare_varname(enumerator)
    {}

enumerator:
| i = enumeration_constant
| i = enumeration_constant EQ_ constant_expression
    { i }

enumeration_constant:
| i = general_identifier
    { set_id_type i VarId; i }

type_qualifier:
| CONST
| RESTRICT
| VOLATILE
| ATOMIC
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
| l=parameter_list COMMA_ ELLIPSIS
    { l }

parameter_list:
| i=parameter_declaration
    { [i] }
| l=parameter_list COMMA_ i=parameter_declaration
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
| identifier_list COMMA_ i = non_type_identifier
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
| LBRACE initializer_list COMMA_? RBRACE
    {}

initializer_list:
| designation? c_initializer
| initializer_list COMMA_ designation? c_initializer
    {}

designation:
| designator_list EQ_
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
| STATIC_ASSERT LPAREN constant_expression COMMA_ string_literal RPAREN SEMICOLON
    {}
*)


statement_dangerous:
| labeled_statement(statement_dangerous)
| in_context(compound_statement)
| expression_statement
| selection_statement_dangerous
| iteration_statement(statement_dangerous)
| jump_statement
| par_statement
    {}

statement_safe:
| labeled_statement(statement_safe)
| in_context(compound_statement)
| expression_statement
| selection_statement_safe
| iteration_statement(statement_safe)
| jump_statement
| par_statement
    {}

labeled_statement(last_statement):
| i = general_identifier COLON last_statement
    { set_id_type i OtherId }
| CASE_ constant_expression COLON last_statement
| DEFAULT_ COLON last_statement
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
| SWITCH_ LPAREN expression RPAREN statement_dangerous
    {}

selection_statement_safe:
| IF LPAREN expression RPAREN statement_safe ELSE statement_safe
| SWITCH_ LPAREN expression RPAREN statement_safe
    {}

iteration_statement(last_statement):
| WHILE_ LPAREN expression RPAREN last_statement
| DO statement_dangerous WHILE_ LPAREN expression RPAREN SEMICOLON
| FOR_ LPAREN expression? SEMICOLON expression? SEMICOLON expression? RPAREN last_statement
| FOR_ LPAREN declaration expression? SEMICOLON expression? RPAREN last_statement
    {}

jump_statement:
| GOTO_ i = general_identifier SEMICOLON
    { set_id_type i OtherId }
| CONTINUE_ SEMICOLON
| BREAK_ SEMICOLON
| RETURN_ expression? SEMICOLON
    {}

(* TODO[non-standard] cppmem thread notation *)
par_statement:
| LBRACES par_statement_list RBRACES
    {}

par_statement_list:
| statement_dangerous
| statement_dangerous BARES par_statement_list
    {}


translation_unit_file:
| translation_unit EOF
    {}
| error
    { Parser_errors.fatal_error "%s:%d:%d Error:@ parse error"
        $startpos.Lexing.pos_fname $startpos.Lexing.pos_lnum $startpos.Lexing.pos_bol }

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
