(* This file is from Jacques-Henri Jourdan's parser *)
%{

module C = Cabs_parser
open List

%}

%token<Cabs_parser.atom * Cabs_parser.cabsloc> VAR_NAME TYPEDEF_NAME OTHER_NAME
%token<Cabs_parser.constant * Cabs_parser.cabsloc> CONSTANT
%token<Cabs_parser.cabsloc> SIZEOF PTR INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ NEQ LT GT
  ANDAND BARBAR PLUS MINUS STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION
  COLON AND

%token<Cabs_parser.cabsloc> MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN SUB_ASSIGN
  LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN XOR_ASSIGN OR_ASSIGN

%token<Cabs_parser.cabsloc> LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE DOT COMMA
  SEMICOLON ELLIPSIS TYPEDEF EXTERN STATIC RESTRICT AUTO REGISTER INLINE
  CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE CONST VOLATILE VOID STRUCT
  UNION ENUM BOOL

%token<Cabs_parser.cabsloc> CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK
  RETURN BUILTIN_VA_ARG

%token EOF

%type<C.expression * C.cabsloc> primary_expression postfix_expression
  unary_expression cast_expression multiplicative_expression additive_expression
  shift_expression relational_expression equality_expression and_expression
  exclusive_OR_expression inclusive_OR_expression logical_AND_expression
  logical_OR_expression conditional_expression assignment_expression
  constant_expression expression
%type<C.unary_operator * C.cabsloc> unary_operator
%type<C.binary_operator> assignment_operator
%type<C.expression list> argument_expression_list
%type<C.definition> declaration
%type<C.spec_elem list * C.cabsloc> declaration_specifiers
%type<C.init_name list> init_declarator_list
%type<C.init_name> init_declarator
%type<C.storage * C.cabsloc> storage_class_specifier
%type<C.typeSpecifier * C.cabsloc> type_specifier struct_or_union_specifier enum_specifier
%type<(C.atom option -> (C.field_group list) option -> C.attribute list -> C.typeSpecifier) * C.cabsloc> struct_or_union
%type<C.field_group list> struct_declaration_list
%type<C.field_group> struct_declaration
%type<C.spec_elem list * C.cabsloc> specifier_qualifier_list
%type<(C.name option * C.expression option) list> struct_declarator_list
%type<C.name option * C.expression option> struct_declarator
%type<(C.atom * C.expression option * C.cabsloc) list> enumerator_list
%type<C.atom * C.expression option * C.cabsloc> enumerator
%type<C.atom * C.cabsloc> enumeration_constant
%type<C.cvspec * C.cabsloc> type_qualifier
%type<C.cabsloc> function_specifier
%type<C.name> declarator direct_declarator
%type<(C.decl_type -> C.decl_type) * C.cabsloc> pointer
%type<C.cvspec list> type_qualifier_list
%type<C.parameter list * bool> parameter_type_list
%type<C.parameter list> parameter_list
%type<C.parameter> parameter_declaration
%type<C.spec_elem list * C.decl_type> type_name
%type<C.decl_type> abstract_declarator direct_abstract_declarator
%type<C.init_expression> c_initializer
%type<(C.initwhat list * C.init_expression) list> initializer_list
%type<C.initwhat list> designation
%type<C.initwhat list> designator_list
%type<C.initwhat> designator
%type<C.statement> statement_dangerous statement_safe 
  labeled_statement(statement_safe) labeled_statement(statement_dangerous)
  iteration_statement(statement_safe) iteration_statement(statement_dangerous)
  compound_statement
%type<C.statement list> block_item_list
%type<C.statement> block_item expression_statement selection_statement_dangerous
  selection_statement_safe jump_statement
%type<C.definition list> translation_unit
%type<C.definition> external_declaration function_definition

%start<Cabs_parser.definition list> translation_unit_file
%%

(* Actual grammar *)

(* 6.5.1 *)
primary_expression:
| var = VAR_NAME
    { (C.VARIABLE (fst var), snd var) }
| cst = CONSTANT
    { (C.CONSTANT (fst cst), snd cst) }
| loc = LPAREN expr = expression RPAREN
    { (fst expr, loc)}

(* 6.5.2 *)
postfix_expression:
| expr = primary_expression
    { expr }
| expr = postfix_expression LBRACK index = expression RBRACK
    { (C.INDEX (fst expr, fst index), snd expr) }
| expr = postfix_expression LPAREN args = argument_expression_list RPAREN
    { (C.CALL (fst expr, rev args), snd expr) }
| expr = postfix_expression LPAREN RPAREN
    { (C.CALL (fst expr, []), snd expr) }
(*
| loc = BUILTIN_VA_ARG LPAREN expr = assignment_expression COMMA ty = type_name RPAREN
    { (BUILTIN_VA_ARG (fst expr, ty), loc) }
*)
| expr = postfix_expression DOT mem = OTHER_NAME
    { (C.MEMBEROF (fst expr, fst mem), snd expr) }
| expr = postfix_expression PTR mem = OTHER_NAME
    { (C.MEMBEROFPTR (fst expr, fst mem), snd expr) }
| expr = postfix_expression INC
    { (C.UNARY (C.POSINCR, fst expr), snd expr) }
| expr = postfix_expression DEC
    { (C.UNARY (C.POSDECR, fst expr), snd expr) }
| loc = LPAREN typ = type_name RPAREN LBRACE init = initializer_list RBRACE
    { (C.CAST (typ, C.COMPOUND_INIT (rev init)), loc) }
| loc = LPAREN typ = type_name RPAREN LBRACE init = initializer_list COMMA RBRACE
    { (C.CAST (typ, C.COMPOUND_INIT (rev init)), loc) }

(* Semantic value is in reverse order. *)
argument_expression_list:
| expr = assignment_expression
    { [fst expr] }
| exprq = argument_expression_list COMMA exprt = assignment_expression
    { fst exprt::exprq }

(* 6.5.3 *)
unary_expression:
| expr = postfix_expression
    { expr }
| loc = INC expr = unary_expression
    { (C.UNARY (C.PREINCR, fst expr), loc) }
| loc = DEC expr = unary_expression
    { (C.UNARY (C.PREDECR, fst expr), loc) }
| op = unary_operator expr = cast_expression
    { (C.UNARY (fst op, fst expr), snd op) }
| loc = SIZEOF expr = unary_expression
    { (C.EXPR_SIZEOF (fst expr), loc) }
| loc = SIZEOF LPAREN typ = type_name RPAREN
    { (C.TYPE_SIZEOF typ, loc) }

unary_operator:
| loc = AND
    { (C.ADDROF, loc) }
| loc = STAR
    { (C.MEMOF, loc) } 
| loc = PLUS
    { (C.PLUS, loc) }
| loc = MINUS
    { (C.MINUS, loc) }
| loc = TILDE
    { (C.BNOT, loc) }
| loc = BANG
    { (C.NOT, loc) }

(* 6.5.4 *)
cast_expression:
| expr = unary_expression
    { expr }
| loc = LPAREN typ = type_name RPAREN expr = cast_expression
    { (C.CAST (typ, C.SINGLE_INIT (fst expr)), loc) }

(* 6.5.5 *)
multiplicative_expression:
| expr = cast_expression
    { expr }
| expr1 = multiplicative_expression STAR expr2 = cast_expression
    { (C.BINARY (C.MUL, fst expr1, fst expr2), snd expr1) }
| expr1 = multiplicative_expression SLASH expr2 = cast_expression
    { (C.BINARY (C.DIV, fst expr1, fst expr2), snd expr1) }
| expr1 = multiplicative_expression PERCENT expr2 = cast_expression
    { (C.BINARY (C.MOD, fst expr1, fst expr2), snd expr1) }

(* 6.5.6 *)
additive_expression:
| expr = multiplicative_expression
    { expr }
| expr1 = additive_expression PLUS expr2 = multiplicative_expression
    { (C.BINARY (C.ADD, fst expr1, fst expr2), snd expr1) }
| expr1 = additive_expression MINUS expr2 = multiplicative_expression
    { (C.BINARY (C.SUB, fst expr1, fst expr2), snd expr1) }

(* 6.5.7 *)
shift_expression:
| expr = additive_expression
    { expr }
| expr1 = shift_expression LEFT expr2 = additive_expression
    { (C.BINARY (C.SHL, fst expr1, fst expr2), snd expr1) }
| expr1 = shift_expression RIGHT expr2 = additive_expression
    { (C.BINARY (C.SHR, fst expr1, fst expr2), snd expr1) }

(* 6.5.8 *)
relational_expression:
| expr = shift_expression
    { expr }
| expr1 = relational_expression LT expr2 = shift_expression
    { (C.BINARY (C.LT, fst expr1, fst expr2), snd expr1) }
| expr1 = relational_expression GT expr2 = shift_expression
    { (C.BINARY (C.GT, fst expr1, fst expr2), snd expr1) }
| expr1 = relational_expression LEQ expr2 = shift_expression
    { (C.BINARY (C.LE, fst expr1, fst expr2), snd expr1) }
| expr1 = relational_expression GEQ expr2 = shift_expression
    { (C.BINARY (C.GE, fst expr1, fst expr2), snd expr1) }

(* 6.5.9 *)
equality_expression:
| expr = relational_expression
    { expr }
| expr1 = equality_expression EQEQ expr2 = relational_expression
    { (C.BINARY (C.EQ, fst expr1, fst expr2), snd expr1) }
| expr1 = equality_expression NEQ expr2 = relational_expression
    { (C.BINARY (C.NE, fst expr1, fst expr2), snd expr1) }

(* 6.5.10 *)
and_expression:
| expr = equality_expression
    { expr }
| expr1 = and_expression AND expr2 = equality_expression
    { (C.BINARY (C.BAND, fst expr1, fst expr2), snd expr1) }

(* 6.5.11 *)
exclusive_OR_expression:
| expr = and_expression
    { expr }
| expr1 = exclusive_OR_expression HAT expr2 = and_expression
    { (C.BINARY (C.XOR, fst expr1, fst expr2), snd expr1) }

(* 6.5.12 *)
inclusive_OR_expression:
| expr = exclusive_OR_expression
    { expr }
| expr1 = inclusive_OR_expression BAR expr2 = exclusive_OR_expression
    { (C.BINARY (C.BOR, fst expr1, fst expr2), snd expr1) }

(* 6.5.13 *)
logical_AND_expression:
| expr = inclusive_OR_expression
    { expr }
| expr1 = logical_AND_expression ANDAND expr2 = inclusive_OR_expression
    { (C.BINARY (C.AND, fst expr1, fst expr2), snd expr1) }

(* 6.5.14 *)
logical_OR_expression:
| expr = logical_AND_expression
    { expr }
| expr1 = logical_OR_expression BARBAR expr2 = logical_AND_expression
    { (C.BINARY (C.OR, fst expr1, fst expr2), snd expr1) }

(* 6.5.15 *)
conditional_expression:
| expr = logical_OR_expression
    { expr }
| expr1 = logical_OR_expression QUESTION expr2 = expression COLON expr3 = conditional_expression
    { (C.QUESTION (fst expr1, fst expr2, fst expr3), snd expr1) }

(* 6.5.16 *)
assignment_expression:
| expr = conditional_expression
    { expr }
| expr1 = unary_expression op = assignment_operator expr2 = assignment_expression
    { (C.BINARY (op, fst expr1, fst expr2), snd expr1) }

assignment_operator:
| EQ
    { C.ASSIGN  }
| MUL_ASSIGN
    { C.MUL_ASSIGN }
| DIV_ASSIGN
    { C.DIV_ASSIGN }
| MOD_ASSIGN
    { C.MOD_ASSIGN }
| ADD_ASSIGN
    { C.ADD_ASSIGN }
| SUB_ASSIGN
    { C.SUB_ASSIGN }
| LEFT_ASSIGN
    { C.SHL_ASSIGN }
| RIGHT_ASSIGN
    { C.SHR_ASSIGN }
| XOR_ASSIGN
    { C.XOR_ASSIGN }
| OR_ASSIGN
    { C.BOR_ASSIGN }
| AND_ASSIGN
    { C.BAND_ASSIGN }

(* 6.5.17 *)
expression:
| expr = assignment_expression
    { expr }
| expr1 = expression COMMA expr2 = assignment_expression
    { (C.BINARY (C.COMMA, fst expr1, fst expr2), snd expr1) }

(* 6.6 *)
constant_expression:
| expr = conditional_expression
    { expr }

(* 6.7 *)
declaration:
| decspec = declaration_specifiers decls = init_declarator_list SEMICOLON
    { C.DECDEF ((fst decspec, rev decls), snd decspec) }
| decspec = declaration_specifiers SEMICOLON
    { C.DECDEF ((fst decspec, []), snd decspec) }

declaration_specifiers:
| storage = storage_class_specifier rest = declaration_specifiers
    { (C.SpecStorage (fst storage)::fst rest, snd storage) }
| storage = storage_class_specifier
    { ([C.SpecStorage (fst storage)], snd storage) }
| typ = type_specifier rest = declaration_specifiers
    { (C.SpecType (fst typ)::fst rest, snd typ) }
| typ = type_specifier
    { ([C.SpecType (fst typ)], snd typ) }
| qual = type_qualifier rest = declaration_specifiers
    { (C.SpecCV (fst qual)::fst rest, snd qual) }
| qual = type_qualifier
    { ([C.SpecCV (fst qual)], snd qual) }
| loc = function_specifier rest = declaration_specifiers
    { (C.SpecInline::fst rest, loc) }
| loc = function_specifier
    { ([C.SpecInline], loc) }

init_declarator_list:
| init = init_declarator
    { [init] }
| initq = init_declarator_list COMMA initt = init_declarator
    { initt::initq }

init_declarator:
| name = declarator
    { C.Init_name (name, C.NO_INIT) }
| name = declarator EQ init = c_initializer
    { C.Init_name (name, init) }

(* 6.7.1 *)
storage_class_specifier:
| loc = TYPEDEF
    { (C.TYPEDEF, loc) }
| loc = EXTERN
    { (C.EXTERN, loc) }
| loc = STATIC
    { (C.STATIC, loc) }
| loc = AUTO
    { (C.AUTO, loc) } 
| loc = REGISTER
    { (C.REGISTER, loc) }

(* 6.7.2 *)
type_specifier:
| loc = VOID
    { (C.Tvoid, loc) }
| loc = CHAR
    { (C.Tchar, loc) }
| loc = SHORT
    { (C.Tshort, loc) }
| loc = INT
    { (C.Tint, loc) }
| loc = LONG
    { (C.Tlong, loc) }
| loc = FLOAT
    { (C.Tfloat, loc) }
| loc = DOUBLE
    { (C.Tdouble, loc) }
| loc = SIGNED
    { (C.Tsigned, loc) }
| loc = UNSIGNED
    { (C.Tunsigned, loc) }
| loc = BOOL
    { (C.T_Bool, loc) }
| spec = struct_or_union_specifier
    { spec }
| spec = enum_specifier
    { spec }
| id = TYPEDEF_NAME
    { (C.Tnamed (fst id), snd id) }

(* 6.7.2.1 *)
struct_or_union_specifier:
| str_uni = struct_or_union id = OTHER_NAME LBRACE decls = struct_declaration_list RBRACE
    { ((fst str_uni) (Some (fst id)) (Some (rev decls)) [], snd str_uni) }
| str_uni = struct_or_union LBRACE decls = struct_declaration_list RBRACE
    { ((fst str_uni) None (Some (rev decls)) [],            snd str_uni) }
| str_uni = struct_or_union id = OTHER_NAME
    { ((fst str_uni) (Some (fst id)) None [],         snd str_uni) }

struct_or_union:
| loc = STRUCT
    { ((fun x y z -> C.Tstruct (x, y, z)), loc) }
| loc = UNION
    { ((fun x y z -> C.Tunion (x, y, z)), loc) }

struct_declaration_list:
| decl = struct_declaration
    { [decl] }
| qdecls = struct_declaration_list tdecls = struct_declaration
    { tdecls::qdecls }

struct_declaration:
| decspec = specifier_qualifier_list decls = struct_declarator_list SEMICOLON
    { C.Field_group (fst decspec, rev decls, snd decspec) }
(* Extension to C99 grammar needed to parse some GNU header files. *)
| decspec = specifier_qualifier_list SEMICOLON
    { C.Field_group (fst decspec, [], snd decspec) }

specifier_qualifier_list:
| typ = type_specifier rest = specifier_qualifier_list
    { (C.SpecType (fst typ)::fst rest, snd typ) }
| typ = type_specifier
    { ([C.SpecType (fst typ)], snd typ) }
| qual = type_qualifier rest = specifier_qualifier_list
    { (C.SpecCV (fst qual)::fst rest, snd qual) }
| qual = type_qualifier
    { ([C.SpecCV (fst qual)], snd qual) }

struct_declarator_list:
| decl = struct_declarator
    { [decl] }
| declq = struct_declarator_list COMMA declt = struct_declarator
    { declt::declq }

struct_declarator:
| decl = declarator
    { (Some decl, None) }
| decl = declarator COLON expr = constant_expression
    { (Some decl, Some (fst expr)) }
| COLON expr = constant_expression
    { (None, Some (fst expr)) }

(* 6.7.2.2 *)
enum_specifier:
| loc = ENUM name = OTHER_NAME LBRACE enum_list = enumerator_list RBRACE
    { (C.Tenum (Some (fst name), Some (rev enum_list), []), loc) }
| loc = ENUM LBRACE enum_list = enumerator_list RBRACE
    { (C.Tenum (None, Some (rev enum_list), []), loc) }
| loc = ENUM name = OTHER_NAME LBRACE enum_list = enumerator_list COMMA RBRACE
    { (C.Tenum (Some (fst name), Some (rev enum_list), []), loc) }
| loc = ENUM LBRACE enum_list = enumerator_list COMMA RBRACE
    { (C.Tenum (None, Some (rev enum_list), []), loc) }
| loc = ENUM name = OTHER_NAME
    { (C.Tenum (Some (fst name), None, []), loc) }

enumerator_list:
| enum = enumerator
    { [enum] }
| enumsq = enumerator_list COMMA enumst = enumerator
    { enumst::enumsq }

enumerator:
| atom = enumeration_constant
    { (fst atom, None, snd atom) }
| atom = enumeration_constant EQ expr = constant_expression
    { (fst atom, Some (fst expr), snd atom) }

enumeration_constant:
| loc = VAR_NAME
    { loc }

(* 6.7.3 *)
type_qualifier:
| loc = CONST
    { (C.CV_CONST, loc) }
| loc = RESTRICT
    { (C.CV_RESTRICT, loc) }
| loc = VOLATILE
    { (C.CV_VOLATILE, loc) }

(* 6.7.4 *)
function_specifier:
| loc = INLINE
    { loc }

(* 6.7.5 *)
declarator:
| decl = direct_declarator
    { decl }
| pt = pointer decl = direct_declarator
    { match decl with C.Name (name, typ, attr, _) -> 
	C.Name (name, (fst pt) typ, attr, snd pt) }

direct_declarator:
| id = VAR_NAME
    { C.Name (fst id, C.JUSTBASE, [], snd id) }
| LPAREN decl = declarator RPAREN
    { decl }
| decl = direct_declarator LBRACK quallst = type_qualifier_list expr = assignment_expression RBRACK
    { match decl with C.Name (name, typ, attr, loc) ->
	C.Name (name, C.ARRAY (typ, rev quallst, [], Some (fst expr)), attr, loc) }
| decl = direct_declarator LBRACK expr = assignment_expression RBRACK
    { match decl with C.Name (name, typ, attr, loc) ->
	C.Name (name, C.ARRAY (typ, [], [], Some (fst expr)), attr, loc) }
| decl = direct_declarator LBRACK quallst = type_qualifier_list RBRACK
    { match decl with C.Name (name, typ, attr, loc) ->
	C.Name (name, C.ARRAY (typ, rev quallst, [], None), attr, loc) }
| decl = direct_declarator LBRACK RBRACK
    { match decl with C.Name (name, typ, attr, loc) ->
	C.Name (name, C.ARRAY (typ, [], [], None), attr, loc) }
(*| direct_declarator LBRACK ... STATIC ... RBRACK
| direct_declarator LBRACK STAR RBRACK*)
| decl = direct_declarator LPAREN params = parameter_type_list RPAREN
    { match decl with C.Name (name, typ, attr, loc) ->
	C.Name (name, C.PROTO (typ, params), attr, loc) }
| decl = direct_declarator LPAREN RPAREN
    { match decl with C.Name (name, typ, attr, loc) ->
        C.Name (name, C.PROTO (typ, ([],false)), attr, loc) }
(* TODO : K&R *)
(*| direct_declarator LPAREN identifier_list RPAREN
    {}*)

pointer:
| loc = STAR
    { ((fun x -> C.PTR ([], [], x)), loc) }
| loc = STAR quallst = type_qualifier_list
    { ((fun x -> C.PTR (rev quallst, [], x)), loc) }
| loc = STAR pt = pointer
    { ((fun typ -> C.PTR ([], [], (fst pt) typ)), loc) }
| loc = STAR quallst = type_qualifier_list pt = pointer
    { ((fun typ -> C.PTR (rev quallst, [], (fst pt) typ)), loc) }

type_qualifier_list:
| qual = type_qualifier
    { [fst qual] }
| qualq = type_qualifier_list qualt = type_qualifier
    { fst qualt::qualq }

parameter_type_list:
| lst = parameter_list
    { (rev lst, false) }
| lst = parameter_list COMMA ELLIPSIS
    { (rev lst, true) }

parameter_list:
| param = parameter_declaration
    { [param] }
| paramq = parameter_list COMMA paramt = parameter_declaration
    { paramt::paramq }

parameter_declaration:
| specs = declaration_specifiers decl = declarator
    { match decl with C.Name (name, typ, attr, _) ->
        C.PARAM (fst specs, Some name, typ, attr, snd specs) }
| specs = declaration_specifiers decl = abstract_declarator
    { C.PARAM (fst specs, None, decl, [], snd specs) }
| specs = declaration_specifiers
    { C.PARAM (fst specs, None, C.JUSTBASE, [], snd specs) }

(* TODO : K&R *)
(*
identifier_list:
| VAR_NAME
| identifier_list COMMA idt = VAR_NAME
    {}
*)

(* 6.7.6 *)
type_name:
| specqual = specifier_qualifier_list
    { (fst specqual, C.JUSTBASE) }
| specqual = specifier_qualifier_list typ = abstract_declarator
    { (fst specqual, typ) }

abstract_declarator:
| pt = pointer
    { (fst pt) C.JUSTBASE }
| pt = pointer typ = direct_abstract_declarator
    { (fst pt) typ }
| typ = direct_abstract_declarator
    { typ }

direct_abstract_declarator:
| LPAREN typ = abstract_declarator RPAREN
    { typ }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list expr = assignment_expression RBRACK
    { C.ARRAY (typ, cvspec, [], Some (fst expr)) }
| LBRACK cvspec = type_qualifier_list expr = assignment_expression RBRACK
    { C.ARRAY (C.JUSTBASE, cvspec, [], Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK expr = assignment_expression RBRACK
    { C.ARRAY (typ, [], [], Some (fst expr)) }
| LBRACK expr = assignment_expression RBRACK
    { C.ARRAY (C.JUSTBASE, [], [], Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list RBRACK
    { C.ARRAY (typ, cvspec, [], None) }
| LBRACK cvspec = type_qualifier_list RBRACK
    { C.ARRAY (C.JUSTBASE, cvspec, [], None) }
| typ = direct_abstract_declarator LBRACK RBRACK
    { C.ARRAY (typ, [], [], None) }
| LBRACK RBRACK
    { C.ARRAY (C.JUSTBASE, [], [], None) }
(*| direct_abstract_declarator? LBRACK STAR RBRACK*)
(*| direct_abstract_declarator? LBRACK ... STATIC ... RBRACK*)
| typ = direct_abstract_declarator LPAREN params = parameter_type_list RPAREN
    { C.PROTO (typ, params) }
| LPAREN params = parameter_type_list RPAREN
    { C.PROTO (C.JUSTBASE, params) }
| typ = direct_abstract_declarator LPAREN RPAREN
    { C.PROTO (typ, ([], false)) }
| LPAREN RPAREN
    { C.PROTO (C.JUSTBASE, ([], false)) }

(* 6.7.8 *)
c_initializer:
| expr = assignment_expression
    { C.SINGLE_INIT (fst expr) }
| LBRACE init = initializer_list RBRACE
    { C.COMPOUND_INIT (rev init) }
| LBRACE init = initializer_list COMMA RBRACE
    { C.COMPOUND_INIT (rev init) }

initializer_list:
| design = designation init = c_initializer
    { [(design, init)] }
| init = c_initializer
    { [([], init)] }
| initq = initializer_list COMMA design = designation init = c_initializer
    { (design, init)::initq }
| initq = initializer_list COMMA init = c_initializer
    { ([], init)::initq }

designation:
| design = designator_list EQ
    { rev design }

designator_list:
| design = designator
    { [design] }
| designq = designator_list designt = designator
    { designt::designq }

designator:
| LBRACK expr = constant_expression RBRACK
    { C.ATINDEX_INIT (fst expr) }
| DOT id = OTHER_NAME
    { C.INFIELD_INIT (fst id) }

(* 6.8 *)
statement_dangerous:
| stmt = labeled_statement(statement_dangerous)
| stmt = compound_statement
| stmt = expression_statement
| stmt = selection_statement_dangerous
| stmt = iteration_statement(statement_dangerous)
| stmt = jump_statement
    { stmt }

statement_safe:
| stmt = labeled_statement(statement_safe)
| stmt = compound_statement
| stmt = expression_statement
| stmt = selection_statement_safe
| stmt = iteration_statement(statement_safe)
| stmt = jump_statement
    { stmt }

(* 6.8.1 *)
labeled_statement(last_statement):
| lbl = OTHER_NAME COLON stmt = last_statement
    { C.LABEL (fst lbl, stmt, snd lbl) }
| loc = CASE expr = constant_expression COLON stmt = last_statement
    { C.CASE (fst expr, stmt, loc) }
| loc = DEFAULT COLON stmt = last_statement
    { C.DEFAULT (stmt, loc) }

(* 6.8.2 *)
compound_statement:
| loc = LBRACE lst = block_item_list RBRACE
    { C.BLOCK (rev lst, loc) }
| loc = LBRACE RBRACE
    { C.BLOCK ([], loc) }

block_item_list:
| stmt = block_item
    { [stmt] }
| stmtq = block_item_list stmtt = block_item
    { stmtt::stmtq }

block_item:
| decl = declaration
    { C.DEFINITION decl }
| stmt = statement_dangerous
    { stmt }

(* 6.8.3 *)
expression_statement:
| expr = expression SEMICOLON
    { C.COMPUTATION (fst expr, snd expr) }
| loc = SEMICOLON
    { C.NOP loc }

(* 6.8.4 *)
selection_statement_dangerous:
| loc = IF LPAREN expr = expression RPAREN stmt = statement_dangerous
    { C.If (fst expr, stmt, None, loc) }
| loc = IF LPAREN expr = expression RPAREN stmt1 = statement_safe ELSE stmt2 = statement_dangerous
    { C.If (fst expr, stmt1, Some stmt2, loc) }
| loc = SWITCH LPAREN expr = expression RPAREN stmt = statement_dangerous
    { C.SWITCH (fst expr, stmt, loc) }

selection_statement_safe:
| loc = IF LPAREN expr = expression RPAREN stmt1 = statement_safe ELSE stmt2 = statement_safe
    { C.If (fst expr, stmt1, Some stmt2, loc) }
| loc = SWITCH LPAREN expr = expression RPAREN stmt = statement_safe
    { C.SWITCH (fst expr, stmt, loc) }

(* 6.8.5 *)
iteration_statement(last_statement):
| loc = WHILE LPAREN expr = expression RPAREN stmt = last_statement
    { C.WHILE (fst expr, stmt, loc) }
| loc = DO stmt = statement_dangerous WHILE LPAREN expr = expression RPAREN SEMICOLON
    { C.DOWHILE (fst expr, stmt, loc) }
| loc = FOR LPAREN expr1 = expression SEMICOLON expr2 = expression SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_EXP (fst expr1)), Some (fst expr2), Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN decl1 = declaration expr2 = expression SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_DECL decl1), Some (fst expr2), Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN SEMICOLON expr2 = expression SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (None, Some (fst expr2), Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN expr1 = expression SEMICOLON SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_EXP (fst expr1)), None, Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN decl1 = declaration SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_DECL decl1), None, Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN SEMICOLON SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { C.FOR (None, None, Some (fst expr3), stmt, loc) }
| loc = FOR LPAREN expr1 = expression SEMICOLON expr2 = expression SEMICOLON RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_EXP (fst expr1)),  Some (fst expr2), None, stmt, loc) }
| loc = FOR LPAREN decl1 = declaration expr2 = expression SEMICOLON RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_DECL decl1), Some (fst expr2), None, stmt, loc) }
| loc = FOR LPAREN SEMICOLON expr2 = expression SEMICOLON RPAREN stmt = last_statement
    { C.FOR (None, Some (fst expr2), None, stmt, loc) }
| loc = FOR LPAREN expr1 = expression SEMICOLON SEMICOLON RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_EXP (fst expr1)), None, None, stmt, loc) }
| loc = FOR LPAREN decl1 = declaration SEMICOLON RPAREN stmt = last_statement
    { C.FOR (Some (C.FC_DECL decl1), None, None, stmt, loc) }
| loc = FOR LPAREN SEMICOLON SEMICOLON RPAREN stmt = last_statement
    { C.FOR (None, None, None, stmt, loc) }

(* 6.8.6 *)
jump_statement:
| loc = GOTO id = OTHER_NAME SEMICOLON
    { C.GOTO (fst id, loc) }
| loc = CONTINUE SEMICOLON
    { C.CONTINUE loc }
| loc = BREAK SEMICOLON
    { C.BREAK loc }
| loc = RETURN expr = expression SEMICOLON
    { C.RETURN (Some (fst expr), loc) }
| loc = RETURN SEMICOLON
    { C.RETURN (None, loc) }

(* 6.9 *)
translation_unit_file:
| lst = translation_unit EOF
    { rev lst }

translation_unit:
| def = external_declaration
    { [def] }
| defq = translation_unit deft = external_declaration
    { deft::defq }

external_declaration:
| def = function_definition
| def = declaration
    { def }

(* 6.9.1 *)
function_definition:
(* TODO : K&R *)
(*| declaration_specifiers declarator declaration_list compound_statement
    {}*)
| specs = declaration_specifiers decl = declarator stmt = compound_statement
    { C.FUNDEF (fst specs, decl, stmt, snd specs) }

(* TODO : K&R 
declaration_list:
| declaration
| declaration_list declaration
    {}
*)
