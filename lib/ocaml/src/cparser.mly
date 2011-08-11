/*(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **)
(**
** 1.0	3.22.99	Hugues Cassé	First version.
** 2.0  George Necula 12/12/00: Practically complete rewrite.
*)
*/
%{
module E = Errormsg
module C = Cabs
module P = Position

let parse_error msg : 'a =
  E.parse_error msg

let print = print_string

let currentFunctionName = ref "<outside any function>"
    
%}

%token <string> IDENT
%token <string> QUALIFIER
%token <int64 list> CONST_CHAR
%token <int64 list> CONST_WCHAR

/* Each character is its own list element, and the terminating nul is not
   included in this list. */
%token <int64 list> CONST_STRING   
%token <int64 list> CONST_WSTRING

%token EOF
%token CHAR INT BOOL VOID
%token ENUM STRUCT UNION
%token SIGNED UNSIGNED LONG SHORT
%token VOLATILE STATIC CONST AUTO

%token SIZEOF ALIGNOF

%token EQ PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ
%token AND_EQ PIPE_EQ CIRC_EQ INF_INF_EQ SUP_SUP_EQ
%token ARROW DOT

%token EQ_EQ EXCLAM_EQ INF SUP INF_EQ SUP_EQ
%token PLUS MINUS STAR
%token SLASH PERCENT
%token TILDE AND
%token PIPE CIRC
%token EXCLAM AND_AND
%token PIPE_PIPE
%token INF_INF SUP_SUP
%token PLUS_PLUS MINUS_MINUS

%token RPAREN 
%token LPAREN RBRACE
%token LBRACE
%token LBRACKET RBRACKET
%token COLON
%token SEMICOLON
%token COMMA QUEST

%token BREAK CONTINUE GOTO RETURN
%token SWITCH CASE DEFAULT
%token WHILE DO FOR
%token IF
%token ELSE
%token INLINE

%token TYPEOF FUNCTION__ PRETTY_FUNCTION__
%token LABEL__

%token<BatBig_int.t * Cabs.suffix option> CONST_INT

/* operator precedence */
%right ELSE
%left	DOT ARROW

/* Non-terminals informations */
%start start
%type <Cabs.g_defn_l list> start

%type <Cabs.stmt_l> statement
%type <Cabs.exp_l> expression
%type <Cabs.exp_l list> argument_expression_list_opt
%type <Cabs.defn_l list> declaration
%%

start:
| translation_unit EOF
    {List.rev $1}
;

/* 6.9#1 External definitions, Syntax */
translation_unit:
| external_declaration
    {[$1]}
/* ATTENTION We store the list in reverse. */
| translation_unit external_declaration
    {$2 :: $1}
;

external_declaration:
| function_definition
    {$1}
| declaration
    {C.EXTERNAL_DECLARATION $1, P.make $startpos $endpos}
;

/* 6.9.1#1 Function definitions, Syntax */
function_definition:
/* TODO No support for old-style function definitions. */
| declaration_specifiers declarator /*declaration_list_opt*/ compound_statement
    { let store, specs, quals = $1 in
      let (name, (mk_type : C.c_type -> C.c_type)), l = $2 in
      let defn_l = (name, mk_type (C.BASE (quals, specs)), store), l in
      C.FUNCTION_DEFINITION (defn_l, $3), P.make $startpos $endpos
    }
;

declaration_list_opt:
| /* empty */
    {[]}
| declaration_list
    {$1}
;

declaration_list:
| declaration
    {[$1]}
/* ATTENTION We store the list in reverse.*/
| declaration_list declaration
    {$2 :: $1}
;

/* 6.5.1#1 Primary expressions, Syntax */
primary_expression:
| identifier
    {C.VARIABLE $1, P.make $startpos $endpos}
| constant
    {C.CONSTANT $1, P.make $startpos $endpos}
| LPAREN expression RPAREN
    {$2}
;

/* 6.5.2#1 Postfix operators, Syntax */
postfix_expression:
| primary_expression     
    {$1}
| postfix_expression LBRACKET expression RBRACKET
    {C.INDEX ($1, $3), P.make $startpos $endpos}
| postfix_expression LPAREN argument_expression_list_opt RPAREN
    {C.CALL ($1, $3), P.make $startpos $endpos}
/* Currently, we have no support for structs.
| postfix_expression DOT identifier
    {C.MEMBEROF (fst $1, fst $3), snd $1}
| postfix_expression ARROW identifier
    {C.MEMBEROFPTR (fst $1, fst $3), snd $1}
*/
| postfix_expression PLUS_PLUS
    {C.UNARY (C.POSTFIX_INCR, $1), P.make $startpos $endpos}
| postfix_expression MINUS_MINUS
    {C.UNARY (C.POSTFIX_DECR, $1), P.make $startpos $endpos}

/* TODO I am omitting compound literals for the moment. Adding them at a later stage shouldn't pose much of a challenge.
| LPAREN type_name RPAREN LBRACE initialiser_list RBRACE
    {C.COMPOUND_LITERAL ($2, C.COMPOUND_INIT $5), $1}
| LPAREN type_name RPAREN LBRACE initialiser_list COMMA RBRACE
    {C.COMPOUND_LITERAL ($2, C.COMPOUND_INIT $5), $1}
*/
;

/* 6.5.3#1 Unary operators, Syntax */
unary_expression:
| postfix_expression
    {$1}
| PLUS_PLUS unary_expression
    {C.UNARY (C.PREFIX_INCR, $2), P.make $startpos $endpos}
| MINUS_MINUS unary_expression
    {C.UNARY (C.PREFIX_DECR, $2), P.make $startpos $endpos}
| unary_operator cast_expression
        {C.UNARY ($1, $2), P.make $startpos $endpos}
/* TODO Not yet supported.
| SIZEOF unary_expression
    {C.EXPR_SIZEOF (fst $2), $1}
*/
| SIZEOF LPAREN type_name RPAREN
    {C.TYPE_SIZEOF $3, P.make $startpos $endpos}
| ALIGNOF LPAREN type_name RPAREN
    {C.TYPE_ALIGNOF $3, P.make $startpos $endpos}
;

unary_operator:
| AND
    {C.ADDRESS}
| STAR
    {C.INDIRECTION}
| PLUS
    {C.PLUS}
| MINUS
    {C.MINUS}
| TILDE
    {C.BNOT}
| EXCLAM
    {C.NOT}
;

/* 6.5.4#1 Cast operators, Syntax */
cast_expression:
| unary_expression
    {$1}
| LPAREN type_name RPAREN cast_expression
    {C.CAST ($2, $4), P.make $startpos $endpos}
;

/* 6.5.5#1 Multiplicative operators, Syntax */
multiplicative_expression:
| cast_expression
    {$1}
| multiplicative_expression STAR cast_expression
    {C.BINARY (C.ARITHMETIC C.MUL, $1, $3), P.make $startpos $endpos}
| multiplicative_expression SLASH cast_expression
    {C.BINARY (C.ARITHMETIC C.DIV, $1, $3), P.make $startpos $endpos}
| multiplicative_expression PERCENT cast_expression
    {C.BINARY (C.ARITHMETIC C.MOD, $1, $3), P.make $startpos $endpos}
;

/* 6.5.6#1 Additive operators, Syntax */
additive_expression:
| multiplicative_expression
    {$1}
| additive_expression PLUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.ADD, $1, $3), P.make $startpos $endpos}
| additive_expression MINUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.SUB, $1, $3), P.make $startpos $endpos}
;

/* 6.5.7 Bitwise shift operators, Syntax */
shift_expression:
| additive_expression
    {$1}
| shift_expression  INF_INF additive_expression
    {C.BINARY (C.ARITHMETIC C.SHL, $1, $3), P.make $startpos $endpos}
| shift_expression  SUP_SUP additive_expression
    {C.BINARY (C.ARITHMETIC C.SHR, $1, $3), P.make $startpos $endpos}
;

/* 6.5.8#1 Relational operators, Syntax */
relational_expression:
| shift_expression
    {$1}
| relational_expression INF shift_expression
    {C.BINARY (C.RELATIONAL C.LT, $1, $3), P.make $startpos $endpos}
| relational_expression SUP shift_expression
    {C.BINARY (C.RELATIONAL C.GT, $1, $3), P.make $startpos $endpos}
| relational_expression INF_EQ shift_expression
    {C.BINARY (C.RELATIONAL C.LE, $1, $3), P.make $startpos $endpos}
| relational_expression SUP_EQ shift_expression
    {C.BINARY (C.RELATIONAL C.GE, $1, $3), P.make $startpos $endpos}
;

/* 6.5.9#1 Equality operators, Syntax */
equality_expression:
| relational_expression
    {$1}
| equality_expression EQ_EQ relational_expression
    {C.BINARY (C.RELATIONAL C.EQ, $1, $3), P.make $startpos $endpos}
| equality_expression EXCLAM_EQ relational_expression
    {C.BINARY (C.RELATIONAL C.NE, $1, $3), P.make $startpos $endpos}
;

/* 6.5.10#1 Bitwise AND operator, Syntax */
and_expression:
| equality_expression
    {$1}
| and_expression AND equality_expression
    {C.BINARY (C.ARITHMETIC C.BAND, $1, $3), P.make $startpos $endpos}
;

/* 6.5.11#1 Bitwise exclusive OR operator */
exclusive_or_expression:
| and_expression
    {$1}
| exclusive_or_expression CIRC and_expression
    {C.BINARY (C.ARITHMETIC C.XOR, $1, $3), P.make $startpos $endpos}
;

/* 6.5.12#1 Bitwise inclusive OR operator */
inclusive_or_expression:
| exclusive_or_expression
    {$1} 
| inclusive_or_expression PIPE exclusive_or_expression
    {C.BINARY (C.ARITHMETIC C.BOR, $1, $3), P.make $startpos $endpos}
;

/* 6.5.13#1 Logical AND operator, Syntax */
logical_and_expression:
| inclusive_or_expression
    {$1}
| logical_and_expression AND_AND inclusive_or_expression
    {C.BINARY (C.SEQUENTIAL C.AND, $1, $3), P.make $startpos $endpos}
;

/* 6.5.14#1 Logical OR operator, Syntax */
logical_or_expression:
| logical_and_expression
    {$1}
| logical_or_expression PIPE_PIPE logical_and_expression
    {C.BINARY (C.SEQUENTIAL C.OR, $1, $3), P.make $startpos $endpos}
;

/* 6.5.15#1 Conditional operator, Syntax*/
conditional_expression:
| logical_or_expression
    { $1 }
| logical_or_expression QUEST expression COLON conditional_expression
    {C.QUESTION ($1, $3, $5), P.make $startpos $endpos}
;

/* 6.5.16#1 Assignment operators, Syntax */
assignment_expression_opt:
| /* empty */
    {None}
| assignment_expression
    {Some $1}
;
assignment_expression:
| conditional_expression
    {$1}
| unary_expression assignment_operator assignment_expression
    {C.ASSIGN ($2, $1, $3), P.make $startpos $endpos}

assignment_operator:
| EQ
    {None}
| STAR_EQ
    {Some C.MUL}
| SLASH_EQ
    {Some C.DIV}
| PERCENT_EQ
    {Some C.MOD}
| PLUS_EQ
    {Some C.ADD}
| MINUS_EQ
    {Some C.SUB}
| INF_INF_EQ
    {Some C.SHL}
| SUP_SUP_EQ
    {Some C.SHR}
| AND_EQ
    {Some C.BAND}
| CIRC_EQ
    {Some C.XOR}
| PIPE_EQ
    {Some C.BOR}
;

/* 6.5.17#1 Comma operator, Syntax */
expression_opt:
| /* empty */
    {None}
| expression
    {Some $1}

expression:
| assignment_expression
    {$1}
| expression COMMA assignment_expression
    {C.BINARY (C.SEQUENTIAL C.COMMA, $1, $3), P.make $startpos $endpos}
;

constant_expression:
| conditional_expression {$1}

  /* 6.4.4#1 Constants, Syntax */
constant:
| integer_constant
    {$1}
/* TODO Add in later.
| CONST_CHAR				{C.CONST_CHAR (fst $1), snd $1}
| CONST_WCHAR				{C.CONST_WCHAR (fst $1), snd $1}
*/
;

integer_constant:
| CONST_INT
    { let value, suffix = $1 in
      C.CONST_INT (value, suffix)
    }
;

/* 6.7.9#1 Initalization, Syntax */
initialiser:
| assignment_expression {$1}
/*
| LBRACE initialiser_list RBRACE {}
| LBRACE initialiser_list COMMA RBRACE {}
*/
;

/*
initialiser_list:
| designation_opt initialiser
    {$2}
*/
/* ATTENTION We store the list in reverse. */
/*
| initialiser_list COMMA designation_opt initialiser
    {$3 :: $1}
;
*/

designation_opt:
| /* empty */
    {}
| designation
    {}

;

designation:
| designator_list EQ {}
;

designator_list:
| designator {}
| designator_list designator {}
;

designator:
| LBRACKET constant_expression RBRACKET {}
| DOT identifier {}
;

/* 6.4.2.1#1 Identifiers - General, Syntax */
identifier:
| IDENT {$1}
;

argument_expression_list_opt:
| /* empty */
    {[]}
| argument_expression_list
    {List.rev $1}
;

argument_expression_list:
| assignment_expression
    {[$1]}
/* ATTENTION Storing list in reverse. Don't forget to reverse the list. */
| argument_expression_list COMMA assignment_expression
    {$3 :: $1}
/* We don't need fancy error handling ;)
| error COMMA argument_expression_list {$3}
*/
;

/* 6.8#1 Statements and blocks, Syntax */
statement:
| labeled_statement
    {$1}
| compound_statement
    {$1}
| expression_statement
    {$1}
| selection_statement
    {$1}
| iteration_statement
    {$1}
| jump_statement
    {$1}
;

/* 6.8.1#1 Labeled statements, Syntax */
labeled_statement:
| identifier COLON statement
    {C.LABEL ($1, $3), P.make $startpos $endpos}
| CASE constant_expression COLON statement
    {C.CASE ($2, $4), P.make $startpos $endpos}
| DEFAULT COLON statement
    {C.DEFAULT ($3), P.make $startpos $endpos}
;

/* 6.8.2#1 Compound statement, Syntax */
compound_statement:
| LBRACE block_item_list_opt RBRACE
    {C.BLOCK ($2), P.make $startpos $endpos}
;

block_item_list_opt:
| /* empty */
    {[]}
| block_item_list
    {List.rev $1}
;

block_item_list:
| block_item
    {[$1]}
/* ATTENTION We are storing the list in reverse. */
| block_item_list block_item
    {$2 :: $1}
;

block_item:
| declaration
    {C.DECLARATION ($1), Position.make $startpos $endpos}
| statement
    {$1}
;

/* 6.8.3#1 Expression and null statement, Syntax */
expression_statement:
| expression_opt SEMICOLON
    { let l = P.make $startpos $endpos in
      match $1 with
      | Some e -> C.EXPRESSION e, l
      | None -> C.SKIP, l
    }
;

/* 6.8.4#1 Selection statements, Syntax */
selection_statement:
| IF LPAREN expression RPAREN statement
    {C.IF ($3, $5, None), P.make $startpos $endpos} %prec ELSE
| IF LPAREN expression RPAREN statement ELSE statement
    {C.IF ($3, $5, Some $7), P.make $startpos $endpos}
| SWITCH LPAREN expression RPAREN statement
    {C.SWITCH ($3, $5), P.make $startpos $endpos}
;

/* 6.8.5#1 Iteration statements, Syntax */
iteration_statement:
| WHILE LPAREN expression RPAREN statement
    {C.WHILE ($3, $5), P.make $startpos $endpos}
| DO statement WHILE LPAREN expression RPAREN
    {C.DO ($5, $2), P.make $startpos $endpos}
| FOR LPAREN expression_opt SEMICOLON expression_opt SEMICOLON expression_opt RPAREN statement
    { let l = P.make $startpos $endpos in
      C.FOR_EXP ($3, $5, $7, $9), l
    }
| FOR LPAREN declaration expression_opt SEMICOLON expression_opt RPAREN
        statement
    { let l = P.make $startpos $endpos in
      C.FOR_DECL ($3, $4, $6, $8), l
    }
;

/* 6.8.6#1 Jump statements, Syntax */
jump_statement:
| GOTO identifier
    {C.GOTO $2, P.make $startpos $endpos}
| CONTINUE SEMICOLON
    {C.CONTINUE, P.make $startpos $endpos}
| BREAK SEMICOLON
    {C.BREAK, P.make $startpos $endpos}
| RETURN expression_opt SEMICOLON
    {C.RETURN $2, P.make $startpos $endpos}
;

/* 6.7#1 Declarations, Syntax */
declaration:
| declaration_specifiers init_declarator_list_opt SEMICOLON
    { let store, specs, quals = $1 in
      let make_def (((name, mk_type), li, exp), lo) =
        (((name, mk_type (C.BASE (quals, specs)), store), li), exp), lo in
      List.map make_def $2
    }
/* TODO We don't support static assertions.
| static_assert_declaration
*/
;

declaration_specifiers_opt:
| /* empty */
    {([], CpMultiSet.empty, BatSet.empty)}
| declaration_specifiers
    {$1}
;

declaration_specifiers:
| storage_class_specifier declaration_specifiers_opt
    { let store, specs, quals = $2 in
      ($1 :: store, specs, quals)
    }
| type_specifier declaration_specifiers_opt
    { let store, specs, quals = $2 in
      (store, CpMultiSet.add $1 specs, quals)
    }
| type_qualifier declaration_specifiers_opt
    { let store, specs, quals = $2 in
      (store, specs, BatSet.add $1 quals)
    }
/* TODO Keyword inline should only be used for function declarations. */
| function_specifier declaration_specifiers_opt
    {$2}
/* TODO _Noreturn is not supported. */
/* TODO We are don't support alignment yet.
| alignment_specifier declaration_specifiers_opt
*/
;

init_declarator_list_opt:
| /* empty */
    {[]}
| init_declarator_list
    {List.rev $1}
;

init_declarator_list:
| init_declarator
    {[$1]}
/* ATTENTION We are storing the list in reverse. */
| init_declarator_list COMMA init_declarator
    {$3 :: $1}
;

init_declarator:
| declarator
    { let name, mk_type = $1 in
      (name, mk_type, None), P.make $startpos $endpos
    }
| declarator EQ initialiser
    { let name, mk_type = $1 in
      (name, mk_type, Some $3), P.make $startpos $endpos
    }

/* 6.7.6#1 Declarators, Syntax */
pointer:
| STAR type_qualifier_list_opt
    {fun t -> C.POINTER ($2, t)}
| STAR type_qualifier_list_opt pointer
    { let mk_type : C.c_type -> C.c_type = $3 in
      fun t -> mk_type (C.POINTER ($2, t))
    }
;

pointer_opt:
| /* empty */
    {fun t -> t}
| pointer
    {$1}
;

type_qualifier_list_opt:
| /* empty */
    {BatSet.empty}
| type_qualifier_list
    {$1}
;

type_qualifier_list:
| type_qualifier
    {BatSet.add $1 BatSet.empty}
| type_qualifier_list type_qualifier
    {BatSet.add $2 $1}
;

/* 6.7.1#1 Storage-class specifier, Syntax */
storage_class_specifier:
/* TODO No support for typedef.
| TYPEDEF
*/
/* TODO No support for extern
| EXTERN
*/
| STATIC
    {C.STATIC}
| AUTO
    {C.AUTO}
/* TODO No support for register
| REGISTER
*/
;

/* 6.7.2#1 Type specifiers, Syntax */
/* TODO Complete the list.*/
type_specifier:
| VOID
    {C.VOID}
| CHAR
    {C.CHAR}    
| SHORT
    {C.SHORT}
| INT
    {C.INT}
| LONG
    {C.LONG}
/*
| FLOAT
| DOUBLE
*/
| SIGNED
    {C.SIGNED}
| UNSIGNED
    {C.UNSIGNED}
| BOOL
    {C.BOOL}
/*
| COMPLEX
*/
/*
| atomic_type_specifier
| struct_or_union_specifier
| enum_specifier
| typedef_specifier
*/
;

/* 6.7.2.1#1 Structure and union specifiers, Syntax */
specifier_qualifier_list_opt:
| /* empty */
    {(CpMultiSet.empty, BatSet.empty)}
| specifier_qualifier_list
    {$1}    
;

specifier_qualifier_list:
| type_specifier specifier_qualifier_list_opt
    { let specs, quals = $2 in
      (CpMultiSet.add $1 specs, quals)
    }
| type_qualifier specifier_qualifier_list_opt
    { let specs, quals = $2 in
      (specs, BatSet.add $1 quals)
    }
;

/* 6.7.3#1 Type qualifiers, Syntax */
type_qualifier:
| CONST {C.CONST}
/*
| RESTRICT
| VOLATILE
| ATOMIC
*/

/* 6.7.4#1 Function specifiers, Syntax */
function_specifier:
| INLINE {()}

/* 6.7.6#1 Declarators, Syntax */
declarator:
| pointer_opt direct_declarator
    { let mk_type1 : C.c_type -> C.c_type = $1 in
      let mk_type2 : C.c_type -> C.c_type = snd $2 in
      (fst $2, fun t -> mk_type2 (mk_type1 t)), P.make $startpos $endpos
    }
;

direct_declarator:
| identifier
    {$1, fun t -> t}
| LPAREN declarator RPAREN
        { let (name, (mk_type : C.c_type -> C.c_type)), _ = $2 in
      name, fun t -> mk_type t
    }
| direct_declarator LBRACKET type_qualifier_list_opt assignment_expression_opt RBRACKET
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> mk_type (C.ARRAY ($3, t, $4))
    }
/* TODO No support for static keyword inside [], nor do we support variable-length arrays. */
| direct_declarator LPAREN parameter_type_list RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, $3)
    }
/* TODO Omitted case handles empty parameter lists. We need a special case. */
| direct_declarator LPAREN RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, [])
    }
| direct_declarator LPAREN VOID RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, [])
    }
/* TODO We do not support function declarations of the following style.
| direct_declarator LPAREN identifier_list_opt RPAREN
*/
;

parameter_type_list:
| parameter_list
    {List.rev $1}
/* TODO No support for functions with a variable number of actuals
| parameter_list COMMA ELLIPSES
*/
;

parameter_list:
| parameter_declaration
    {[$1]}
/* ATTENTION We are storing the list in reverse. */
| parameter_list COMMA parameter_declaration
    {$3 :: $1}
;

parameter_declaration:
| declaration_specifiers declarator
    { let (name, (mk_type : C.c_type -> C.c_type)), l = $2 in
      let store, specs, quals = $1 in
      (name, mk_type (C.BASE (quals, specs)), store), l
    }
/* TODO No support for type-only parameters yet. Important since we need main (void).
| declaration_specifiers abstract_declarator_opt
    { let mk_type : C.c_type -> C.c_type = $2 in
      let store, quals, specs = $1 in
      (name, mk_type (C.BASE (quals, specs)), store, None)
    }
*/
;

/* 6.7.7#1 Type names, Syntax */
type_name:
| specifier_qualifier_list abstract_declarator_opt
    { let specs, quals = $1 in
      $2 (C.BASE (quals, specs))
    }
;

abstract_declarator_opt:
| /* empy */
    {fun t -> t}
| abstract_declarator
    {$1}
;

abstract_declarator:
| pointer
    {$1}
| pointer_opt direct_abstract_declarator
    { let mk_type1 : C.c_type -> C.c_type = $1 in
      let mk_type2 : C.c_type -> C.c_type = $2 in
      fun t -> mk_type2 (mk_type1 t)
    }
;

direct_abstract_declarator_opt:
| /* empty */
    {fun t -> t}
| direct_abstract_declarator
    {$1}
;

direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN
    {  let mk_type : C.c_type -> C.c_type = $2 in
       fun t -> mk_type t
    }
| direct_abstract_declarator_opt LBRACKET type_qualifier_list_opt assignment_expression_opt RBRACKET
    { let mk_type : C.c_type -> C.c_type = $1 in
      fun t -> mk_type (C.ARRAY ($3, t, $4))
    }
/* TODO Add the other constructs including function pointers. */
;

%%
