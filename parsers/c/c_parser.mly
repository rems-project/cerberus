(* Grammar based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 *
 * NOTE: we parameterise the declarator rules to avoid the conflicts left
 * in their grammar (see parameter_declarator_varname). *)

%{
open Cerb_frontend

open Cabs
open Cn

module LF = Lexer_feedback

let pos x = C_lexer.LineMap.position x
let region (x,y) p = Cerb_location.region (pos x, pos y) p
let point x = Cerb_location.point (pos x)
let noCursor = Cerb_location.NoCursor
let pointCursor x = Cerb_location.PointCursor (pos x)

let id =
  fun z -> z

let opt_to_rev_list = function
  | None -> []
  | Some xs -> List.rev xs

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

let string_of_cabs_id (Symbol.Identifier(_, n)) = n

let to_attrs = function
  | None ->
      Annot.Attrs []
  | Some z ->
      Annot.Attrs begin
        List.map (fun ((ns, id), args_opt) ->
          let open Annot in
          { attr_ns=   ns
          ; attr_id=   id
          ; attr_args= match args_opt with None -> [] | Some z -> z }
        ) (List.concat (List.rev z))
      end

let inject_attr attr_opt (CabsStatement (loc, Annot.Attrs xs, stmt_)) =
  let Annot.Attrs xs' = to_attrs attr_opt in
  CabsStatement (loc, Annot.Attrs (xs @ xs'), stmt_)

let magic_to_attr magik : Annot.attribute =
  let open Annot in
  { attr_ns= Some (Symbol.Identifier (Cerb_location.unknown, "cerb"))
  ; attr_id= Symbol.Identifier (Cerb_location.unknown, "magic")
  ; attr_args= List.map (fun (loc, (_,str)) -> (loc, str, [loc, str])) magik }

let magic_to_attrs = function
  | [] ->
      Annot.Attrs []
  | magic ->
      Annot.Attrs [magic_to_attr magic]

let magic_to_opt_attrs = function
  | [] -> None
  | magic -> Some (magic_to_attrs magic)

let opt_magic_to_opt_attrs = function
  | None -> None
  | Some magic -> Some (magic_to_attrs [magic])

(* use this to show a warning when a NON-STD 'extra' semicolon was parsed *)
let warn_extra_semicolon pos ctx =
  if not M.warn_extra_semicolon then
    prerr_endline (Pp_errors.make_message
                    (point pos)
                    Errors.(C_PARSING (Cparser_extra_semi ctx))
                    Warning)
  else
    ()
%}

(* §6.4.1 keywords *)
%token AUTO (*BREAK CASE*) CHAR CONST (*CONTINUE DEFAULT DO*) DOUBLE ELSE ENUM EXTERN
  FLOAT (*FOR GOTO IF*) INLINE INT LONG REGISTER RESTRICT (*RETURN*) SHORT SIGNED SIZEOF
  STATIC STRUCT (*SWITCH*) TYPEDEF UNION UNSIGNED VOID VOLATILE (*WHILE*) ALIGNAS
  ALIGNOF ATOMIC BOOL COMPLEX GENERIC (* IMAGINARY *) NORETURN STATIC_ASSERT
  THREAD_LOCAL
%token BREAK CASE CONTINUE DEFAULT DO FOR GOTO IF RETURN SWITCH WHILE

(* §6.4.2 Identifiers *)
%token<string> NAME
%token VARIABLE TYPE

(* §6.4.4 Constants *)
%token<Cabs.cabs_constant> CONSTANT

(* §6.4.5 String literals *)
(* NOTE: adjacent string literals are concatenated by the lexer
 * (see C_lexer.create_lexer) *)
%token<Cabs.cabs_string_literal> STRING_LITERAL

(* §6.4.6 Punctuators *)
%token LBRACK RBRACK LPAREN RPAREN (*LBRACE RBRACE*) DOT MINUS_GT
  PLUS_PLUS MINUS_MINUS AMPERSAND STAR PLUS MINUS TILDE BANG
  SLASH PERCENT LT_LT GT_GT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET PIPE
  AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON (*SEMICOLON*) ELLIPSIS EQ STAR_EQ SLASH_EQ PERCENT_EQ COLON_COLON
  PLUS_EQ MINUS_EQ LT_LT_EQ GT_GT_EQ AMPERSAND_EQ CARET_EQ PIPE_EQ COMMA
  LBRACK_LBRACK (*RBRACK_RBRACK*)
%token LBRACE RBRACE SEMICOLON

(* C23 keywords *)
%token BITINT CONSTEXPR DECIMAL32 DECIMAL64 DECIMAL128 FALSE NULLPTR TYPEOF
  TRUE TYPEOF_UNQUAL

(* GNU keywords *)
%token ATTRIBUTE AUTO_TYPE EXTENSION INT128 LABEL

(* Builtin requiring special parsing *)
  BUILTIN_ASSERT BUILTIN_OFFSETOF BUILTIN_TYPES_COMPATIBLE_P BUILTIN_CHOOSE_EXPR

(* NON-STD cppmem syntax *)
  LBRACES PIPES RBRACES

%token VA_START VA_COPY VA_ARG VA_END PRINT_TYPE ASM

(* BMC syntax *)
%token BMC_ASSUME

(* magic comment token *)
%token<Cerb_location.t * (char * string)> CERB_MAGIC

%token EOF

%nonassoc THEN
%nonassoc ELSE


(* ========================================================================== *)

%type<string> typedef_name var_name
%type<Symbol.identifier> general_identifier

%type<LF.context> save_context

%type<LF.declarator>
  declarator
  declarator_varname
  declarator_typedefname
  parameter_declarator_varname

%type<Symbol.identifier>
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

%type<Cabs.cabs_declaration>
  no_leading_attribute_declaration

%type<Cabs.cabs_declaration>
  declaration

%type<Cabs.cabs_declaration>
  declaration_ext

%type<Cabs.specifiers>
  declaration_specifiers

%type<Cabs.storage_class_specifier>
  storage_class_specifier

%type<Cabs.cabs_type_specifier>
  struct_or_union_specifier

%type<Annot.attributes -> Symbol.identifier option -> (Cabs.struct_declaration list) option -> Lexing.position -> Cabs.cabs_type_specifier>
  struct_or_union

%type<Cabs.struct_declaration list>
  struct_declaration_list

%type<Cabs.struct_declaration>
  struct_declaration

%type<Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list * Cabs.alignment_specifier list>
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

%type<Cerb_location.t * string * (Cerb_location.t * string) list>
  located_string_literal

%start<Cerb_frontend.Cabs.translation_unit> translation_unit

%parameter<
  M : sig
    val warn_extra_semicolon: bool
  end
>

%% (* ======================================================================= *)

translation_unit: (* NOTE: this is not present in the standard *)
| EOF
    { TUnit [] }
| edecls= external_declaration_list EOF
    { TUnit (List.rev edecls) }
;

(* A pair of lists of exactly one A *)
list_eq1(A, B):
| a=A bs=B*
    { ([a], bs) }
| b=B rest=list_eq1(A, B)
    { let (ax, bs) = rest in (ax, b::bs) }
;

(* A pair of lists of at least one A *)
list_ge1(A, B):
| a=A bs=B*
    { ([a], bs) }
| a=A rest=list_ge1(A, B)
    { let (ax, bs) = rest in (a::ax, bs) }
| b=B rest=list_ge1(A, B)
    { let (ax, bs) = rest in (ax, b::bs) }
;

(* A record of lists of exactly one A and one B *)
list_eq1_eq1(A, B, C):
| a=A rest=list_eq1(B, C)
    { let (bs, cs) = rest in ([a], bs, cs) }
| b=B rest=list_eq1(A, C)
    { let (ax, cs) = rest in (ax, [b], cs) }
| c=C rest=list_eq1_eq1(A, B, C)
    { let (ax, bs, cs) = rest in (ax, bs, c::cs) }
;

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
;

(* Pair of lists *)
list_pair(A, B):
|
  { ([], []) }
| a=A rest=list_pair(A, B)
  { let (ax, bx) = rest in (a::ax, bx) }
| b=B rest=list_pair(A, B)
  { let (ax, bx) = rest in (ax, b::bx) }
;

(* A record of lists of exactly one A *)
list_tuple3_eq1(A, B, C):
| a=A rest=list_pair(B, C)
  { let (bx, cx) = rest in ([a], bx, cx) }
| b=B rest=list_tuple3_eq1(A, B, C)
  { let (ax, bx, cx) = rest in (ax, b::bx, cx) }
| c=C rest=list_tuple3_eq1(A, B, C)
  { let (ax, bx, cx) = rest in (ax, bx, c::cx) }
;

(* A record of lists of at least one A *)
list_tuple3_ge1(A, B, C):
| a=A rest=list_pair(B, C)
  { let (bx, cx) = rest in ([a], bx, cx) }
| a=A rest=list_tuple3_ge1(A, B, C)
  { let (ax, bx, cx) = rest in (a::ax, bx, cx) }
| b=B rest=list_tuple3_ge1(A, B, C)
  { let (ax, bx, cx) = rest in (ax, b::bx, cx) }
| c=C rest=list_tuple3_ge1(A, B, C)
  { let (ax, bx, cx) = rest in (ax, bx, c::cx) }
;

(* Identifiers and lexer feedback contexts *)
typedef_name:
| n= NAME TYPE
    { n }
;

var_name:
| n= NAME VARIABLE
    { n }
;

typedef_name_spec:
| i= typedef_name
    { TSpec ((region ($startpos, $endpos) noCursor),
             TSpec_name (Identifier (point $startpos, i))) }
;

general_identifier:
| i= typedef_name
| i= var_name
    { Symbol.Identifier (region ($startpos, $endpos) noCursor, i) }
;

save_context:
| (* empty *)
  { LF.save_context () }
;

scoped(X):
| ctxt=save_context x=X
    { LF.restore_context ctxt; x }
;

declarator_varname:
| decl = declarator
    { LF.declare_varname (LF.identifier decl); decl }
;

declarator_typedefname:
| decl = declarator
    { LF.declare_typedefname (LF.identifier decl); decl }
;

(* STD §6.7.6.3#11: "If, in a parameter declaration, an identifier can be
 * treated either as a typedef name or as a parameter name, it shall be taken
 * as a typedef name."
 * This happens when a typedef name is the first token of a parenthesised
 * declarator, e.g. in [int f(int (T));], where [(T)] can either be a
 * parenthesised declarator for a parameter named T or (taken here) the
 * parameter list of an abstract function declarator. So the identifier of a
 * parenthesised declarator in a parameter declaration cannot be a typedef name.
 * After a pointer, as in [int f(int ( *T))], T can only be a parameter name. *)
parameter_declarator_varname:
| decl = declarator_(general_identifier, var_identifier)
    { LF.declare_varname (LF.identifier decl); decl }
;

var_identifier:
| i= var_name
    { Symbol.Identifier (region ($startpos, $endpos) noCursor, i) }
;

(* §6.4.4.3 Enumeration constants Primary expressions *)
enumeration_constant:
| i= general_identifier
    { LF.declare_varname (string_of_cabs_id i); i }
;

(* §6.5.1 Primary expressions *)
primary_expression:
| str= var_name
    { CabsExpression (region ($startpos, $endpos) noCursor,
        CabsEident (Symbol.Identifier (point $startpos(str), str))) }
| cst= CONSTANT
    { CabsExpression (region ($startpos, $endpos) noCursor,
                      CabsEconst cst) }
| lit= STRING_LITERAL
    { CabsExpression (region ($startpos, $endpos) noCursor,
                      CabsEstring lit) }
| LPAREN expr= expression RPAREN
    { let CabsExpression (_, expr_) = expr in
      CabsExpression (region ($startpos, $endpos) noCursor, expr_ ) }
| gs= generic_selection
    { gs }
(* GCC extension: Statement Exprs *)
// | LPAREN stmt= scoped(compound_statement) RPAREN
| LPAREN LBRACE bis_opt= block_item_list? RBRACE RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEgcc_statement (opt_to_rev_list bis_opt) ) }
;

(* §6.5.1.1 Generic selection *)
generic_selection:
| GENERIC LPAREN expr= assignment_expression COMMA gas= generic_assoc_list RPAREN
    { CabsExpression (region ($startpos, $endpos) noCursor,
        CabsEgeneric (expr, gas)) }
;

generic_assoc_list: (* NOTE: the list is in reverse *)
| ga= generic_association
    { [ga] }
| gas= generic_assoc_list COMMA ga= generic_association
    { ga::gas }
;

generic_association:
| ty= type_name COLON expr= assignment_expression
    { GA_type (ty, expr) }
| DEFAULT COLON expr= assignment_expression
    { GA_default expr }
;

(* §6.5.2 Postfix operators *)
postfix_expression:
| expr= primary_expression
    { expr }
| expr1= postfix_expression LBRACK expr2= expression RBRACK
    { CabsExpression ( region ($startpos, $endpos) noCursor
                     , CabsEsubscript (expr1, expr2) ) }
| expr= postfix_expression LPAREN exprs_opt= argument_expression_list? opt_magic=option(CERB_MAGIC) RPAREN
    { CabsExpression ( region ($startpos, $endpos) noCursor
                     , CabsEcall (expr, opt_to_rev_list exprs_opt, opt_magic_to_opt_attrs opt_magic) ) }
| expr= postfix_expression DOT i= general_identifier
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEmemberof (expr, i) ) }
| expr= postfix_expression MINUS_GT i= general_identifier
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEmemberofptr (expr, i) ) }
| expr= postfix_expression PLUS_PLUS
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEpostincr expr ) }
| expr= postfix_expression MINUS_MINUS
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEpostdecr expr ) }
| LPAREN ty= type_name RPAREN LBRACE inits= initializer_list COMMA? RBRACE
    { CabsExpression (region ($startpos, $endpos) noCursor,
                      CabsEcompound (ty, List.rev inits)) }
(* NOTE: non-std way of dealing with these *)
| BUILTIN_ASSERT LPAREN expr= assignment_expression RPAREN
    { CabsExpression (region ($startpos, $endpos) noCursor,
                      CabsEassert expr) }
| VA_START LPAREN expr= assignment_expression COMMA i= general_identifier RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEva_start(expr, i) ) }
| VA_COPY LPAREN e1= assignment_expression COMMA e2= assignment_expression RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEva_copy(e1, e2) ) }
| VA_ARG LPAREN expr= assignment_expression COMMA ty= type_name RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEva_arg(expr, ty) ) }
| VA_END LPAREN expr= assignment_expression RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEva_end(expr) ) }
| BUILTIN_OFFSETOF LPAREN ty= type_name COMMA i= general_identifier RPAREN
    { CabsExpression ( region ($startpos, $endpos) noCursor
                     , CabsEoffsetof (ty, i) ) }
| BUILTIN_TYPES_COMPATIBLE_P LPAREN ty1= type_name COMMA ty2= type_name RPAREN
    { CabsExpression ( region ($startpos, $endpos) noCursor
                     , CabsEbuiltinGNU (GNUbuiltin_types_compatible_p (ty1, ty2)) ) }
| BUILTIN_CHOOSE_EXPR LPAREN const_e= assignment_expression COMMA e1= assignment_expression COMMA e2= assignment_expression RPAREN
    { CabsExpression ( region ($startpos, $endpos) noCursor
                     , CabsEbuiltinGNU (GNUbuiltin_choose_expr (const_e, e1, e2)) ) }
(* NOTE: the following is a cerb extension allowing the user to the
   query the type of an expression  *)
| PRINT_TYPE LPAREN expr= expression RPAREN
   { CabsExpression (region ($startpos, $endpos) noCursor,
        CabsEprint_type expr) }
| BMC_ASSUME LPAREN expr= assignment_expression RPAREN
    { CabsExpression (region ($startpos, $endpos) noCursor,
                      CabsEbmc_assume expr) }
;

argument_expression_list: (* NOTE: the list is in reverse *)
| expr= assignment_expression
    { [expr] }
| exprs= argument_expression_list COMMA expr= assignment_expression
    { expr::exprs }
;

(* §6.5.3 Unary operators *)
unary_expression:
| expr= postfix_expression
    { expr }
| PLUS_PLUS expr= unary_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEpreincr expr ) }
| MINUS_MINUS expr= unary_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEpredecr expr ) }
| op= unary_operator expr= cast_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos(op))
                     , CabsEunary (op, expr) ) }
| EXTENSION expr= cast_expression
    { expr }
| SIZEOF expr= unary_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEsizeof_expr expr ) }
| SIZEOF LPAREN ty= type_name RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEsizeof_type ty ) }
| ALIGNOF LPAREN ty= type_name RPAREN
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEalignof ty ) }
| AMPERSAND_AMPERSAND l= general_identifier
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsElabel_addressGNU l ) }
;

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
;

(* §6.5.4 Cast operators *)
cast_expression:
| expr= unary_expression
    { expr }
| LPAREN ty= type_name RPAREN expr= cast_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($1))
                     , CabsEcast (ty, expr) ) }
;

(* §6.5.5 Multiplicative operators *)
multiplicative_expression:
| expr= cast_expression
    { expr }
| expr1= multiplicative_expression STAR expr2= cast_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsMul, expr1, expr2) ) }
| expr1= multiplicative_expression SLASH expr2= cast_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsDiv, expr1, expr2) ) }
| expr1= multiplicative_expression PERCENT expr2= cast_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsMod, expr1, expr2) ) }
;

(* §6.5.6 Additive operators *)
additive_expression:
| expr= multiplicative_expression
    { expr }
| expr1= additive_expression PLUS expr2= multiplicative_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsAdd, expr1, expr2) ) }
| expr1= additive_expression MINUS expr2= multiplicative_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsSub, expr1, expr2) ) }
;

(* §6.5.7 Bitwise shift operators *)
shift_expression:
| expr= additive_expression
    { expr }
| expr1= shift_expression LT_LT expr2= additive_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsShl, expr1, expr2) ) }
| expr1= shift_expression GT_GT expr2= additive_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsShr, expr1, expr2) ) }
;

(* §6.5.8 Relational operators *)
relational_expression:
| expr= shift_expression
    { expr }
| expr1= relational_expression LT expr2= shift_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsLt, expr1, expr2) ) }
| expr1= relational_expression GT expr2= shift_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsGt, expr1, expr2) ) }
| expr1= relational_expression LT_EQ expr2= shift_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsLe, expr1, expr2) ) }
| expr1= relational_expression GT_EQ expr2= shift_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsGe, expr1, expr2) ) }
;

(* §6.5.9 Equality operators *)
equality_expression:
| expr= relational_expression
    { expr }
| expr1= equality_expression EQ_EQ expr2= relational_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsEq, expr1, expr2) ) }
| expr1= equality_expression BANG_EQ expr2= relational_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsNe, expr1, expr2) ) }
;

(* §6.5.10 Bitwise AND operator *)
_AND_expression:
| expr= equality_expression
    { expr }
| expr1= _AND_expression AMPERSAND expr2= equality_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsBand, expr1, expr2) ) }
;

(* §6.5.11 Bitwise exclusive OR operator *)
exclusive_OR_expression:
| expr= _AND_expression
    { expr }
| expr1= exclusive_OR_expression CARET expr2= _AND_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsBxor, expr1, expr2) ) }
;

(* §6.5.12 Bitwise inclusive OR operator *)
inclusive_OR_expression:
| expr= exclusive_OR_expression
    { expr }
| expr1= inclusive_OR_expression PIPE expr2= exclusive_OR_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsBor, expr1, expr2) ) }
;

(* §6.5.13 Logical AND operator *)
logical_AND_expression:
| expr= inclusive_OR_expression
    { expr }
| expr1=logical_AND_expression AMPERSAND_AMPERSAND expr2=inclusive_OR_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsAnd, expr1, expr2) ) }
;

(* §6.5.14 Logical OR operator *)
logical_OR_expression:
| expr= logical_AND_expression
    { expr }
| expr1= logical_OR_expression PIPE_PIPE expr2= logical_AND_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEbinary (CabsOr, expr1, expr2) ) }
;

(* §6.5.15 Conditional operator *)
conditional_expression:
| expr= logical_OR_expression
    { expr }
| expr1= logical_OR_expression QUESTION expr2= expression
                               COLON    expr3= conditional_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEcond (expr1, expr2, expr3) ) }
| expr1= logical_OR_expression QUESTION COLON expr2= conditional_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEcondGNU (expr1, expr2) ) }
;

(* §6.5.16 Assignment operators *)
assignment_expression:
| expr= conditional_expression
    { expr }
| expr1= unary_expression op= assignment_operator expr2= assignment_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos(op))
                     , CabsEassign (op, expr1, expr2) ) }
;

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
;

(* §6.5.17 Comma operator *)
expression:
| expr= assignment_expression
    { expr }
| expr1= expression COMMA expr2= assignment_expression
    { CabsExpression ( region ($startpos, $endpos) (pointCursor $startpos($2))
                     , CabsEcomma (expr1, expr2) ) }
;

(* §6.6 Constant expressions *)
constant_expression:
| expr= conditional_expression
    { expr }
;

(* §6.7 Declarations *)
no_leading_attribute_declaration:
| decspecs= declaration_specifiers
    idecls_opt= init_declarator_list(declarator_varname)? SEMICOLON
    { Declaration_base (Annot.no_attributes, decspecs, opt_to_rev_list idecls_opt) }
| decspecs= declaration_specifiers_typedef
    idecls_opt= init_declarator_list(declarator_typedefname)? SEMICOLON
    { Declaration_base (Annot.no_attributes, decspecs, opt_to_rev_list idecls_opt) }
| sa= static_assert_declaration
    { Declaration_static_assert sa }
;

declaration:
| xs_decl= no_leading_attribute_declaration
    { xs_decl }
| attr= attribute_specifier_sequence decspecs= declaration_specifiers
    idecls_opt= init_declarator_list(declarator_varname)? SEMICOLON
    { Declaration_base (to_attrs (Some attr), decspecs, opt_to_rev_list idecls_opt) }
| attr= attribute_specifier_sequence decspecs= declaration_specifiers_typedef
    idecls_opt= init_declarator_list(declarator_typedefname)? SEMICOLON
    { Declaration_base (to_attrs (Some attr), decspecs, opt_to_rev_list idecls_opt) }
| attribute_declaration
    { (*TODO: this is a dummy declaration*)
      let loc = region($startpos, $endpos) (pointCursor $startpos) in
      Declaration_base (Annot.no_attributes, empty_specs, [InitDecl (loc, Declarator (None, DDecl_identifier (Annot.no_attributes, Symbol.Identifier (loc, "test"))), None)]) }
;

(* GNU extension: a declaration in a compound statement or in a for clause can
 * be preceded by __extension__ *)
declaration_ext:
| xs_decl= declaration
    { xs_decl }
| EXTENSION xs_decl= declaration_ext
    { xs_decl }
;

declaration_specifier:
| sc= storage_class_specifier ioption(attribute_specifier_sequence)
    { { empty_specs with storage_classes=      [sc]; } }
| tq= type_qualifier ioption(attribute_specifier_sequence)
    { { empty_specs with type_qualifiers=      [tq]; } }
| fs= function_specifier ioption(attribute_specifier_sequence)
    { { empty_specs with function_specifiers=  [fs]; } }
| als= alignment_specifier ioption(attribute_specifier_sequence)
    { { empty_specs with alignment_specifiers= [als]; } }
;

declaration_specifiers:
| ts_specs= list_eq1(attribute_type_specifier_unique, declaration_specifier)
| ts_specs= list_ge1(attribute_type_specifier_nonunique, declaration_specifier)
    { let (ts, ss) = ts_specs in
      { (concat_specs ss) with type_specifiers= ts; } }
;

declaration_specifiers_typedef:
| ts_specs= list_eq1_eq1(TYPEDEF,attribute_type_specifier_unique,
                         declaration_specifier)
| ts_specs= list_eq1_ge1(TYPEDEF,attribute_type_specifier_nonunique,
                         declaration_specifier)
    { let (_, ts, ss) = ts_specs in
      let specs = concat_specs ss in
      { specs with storage_classes= SC_typedef::specs.storage_classes;
                   type_specifiers= ts; } }
;

init_declarator_list(declarator): (* NOTE: the list is in reverse *)
| idecl= init_declarator(declarator)
    { [idecl] }
| idecls= init_declarator_list(declarator)
    COMMA idecl= init_declarator(declarator)
    { idecl::idecls }
;

init_declarator(declarator):
| decl= declarator ioption(asm_register)
    { InitDecl (region ($startpos, $endpos) noCursor,
                LF.cabs_of_declarator decl, None) }
| decl= declarator ioption(asm_register) EQ init= initializer_
    { InitDecl (region ($startpos, $endpos) noCursor,
                LF.cabs_of_declarator decl, Some init) }
;

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
;

(* §6.7.2 Type specifiers *)
type_specifier_nonunique:
| CHAR
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_char) }
| SHORT
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_short) }
| INT
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_int) }
| LONG
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_long) }
| FLOAT
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_float) }
| DOUBLE
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_double) }
| SIGNED
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_signed) }
| UNSIGNED
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_unsigned) }
| COMPLEX
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_Complex) }
;

attribute_type_specifier_nonunique:
| ty= type_specifier_nonunique ioption(attribute_specifier_sequence)
    { ty }
;

type_specifier_unique:
| VOID
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_void) }
| BOOL
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_Bool) }
| spec= atomic_type_specifier
    { spec }
| spec= struct_or_union_specifier
    { spec }
| spec= enum_specifier
    { spec }
| spec= typedef_name_spec
    { spec }
| TYPEOF LPAREN expr= expression RPAREN
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_typeof_expr expr) }
| TYPEOF LPAREN ty= type_name RPAREN
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_typeof_type ty) }
;

attribute_type_specifier_unique:
| ty= type_specifier_unique ioption(attribute_specifier_sequence)
    { ty }
;

(* §6.7.2.1 Structure and union specifiers *)
struct_or_union_specifier:
| ctor= struct_or_union attr_opt= attribute_specifier_sequence?
    iopt= general_identifier? LBRACE has_extra= boption(SEMICOLON+) rev_decls= struct_declaration_list RBRACE
    { if has_extra then warn_extra_semicolon $startpos(has_extra) INSIDE_STRUCT;
      ctor (to_attrs attr_opt) iopt (Some (List.rev rev_decls)) $endpos }
| ctor= struct_or_union attr_opt= attribute_specifier_sequence?
    i= general_identifier
    { ctor (to_attrs attr_opt) (Some i) None $endpos }
| ctor= struct_or_union attr_opt= attribute_specifier_sequence?
    iopt= general_identifier? LBRACE RBRACE
    (* GCC extension *)
    (* TODO: forbid union *)
    { ctor (to_attrs attr_opt) iopt (Some []) $endpos }
;

struct_or_union:
| STRUCT
    { fun attrs x y epos -> TSpec (region ($startpos, epos) noCursor,
                              TSpec_struct (attrs, x, y)) }
| UNION
    { fun attrs x y epos -> TSpec (region ($startpos, epos) noCursor,
                              TSpec_union (attrs, x, y)) }
;

struct_declaration_list: (* NOTE: the list is in reverse *)
| sdecl= struct_declaration
    { [sdecl] }
| sdecls= struct_declaration_list sdecl= struct_declaration
    { sdecl::sdecls }
;

struct_declaration:
| attr_opt= ioption(attribute_specifier_sequence) tspecs_tquals= specifier_qualifier_list
    rev_sdeclrs_opt= struct_declarator_list? SEMICOLON has_extra= boption(SEMICOLON+)
    { if has_extra then warn_extra_semicolon $startpos(has_extra) INSIDE_STRUCT;
      let (tspecs, tquals, align_specs) = tspecs_tquals in
      Struct_declaration (to_attrs attr_opt, tspecs, tquals, align_specs,
                          opt_to_rev_list rev_sdeclrs_opt) }
| sa_decl= static_assert_declaration
    { Struct_assert sa_decl }
| EXTENSION decl= struct_declaration
    { decl }
;

specifier_qualifier_list:
| tspecs_tquals= list_tuple3_eq1 (attribute_type_specifier_unique,
                                  attribute_type_qualifier,
                                  attribute_alignment_specifier)
| tspecs_tquals= list_tuple3_ge1 (attribute_type_specifier_nonunique,
                                  attribute_type_qualifier,
                                  attribute_alignment_specifier)
    { tspecs_tquals }
;

struct_declarator_list: (* NOTE: the list is in reverse *)
| sdelctor= struct_declarator
    { [sdelctor] }
| sdecltors= struct_declarator_list COMMA sdecltor= struct_declarator
    { sdecltor::sdecltors }
;

struct_declarator:
| decltor= declarator
    { SDecl_simple (LF.cabs_of_declarator decltor) }
| decltor_opt= declarator? COLON expr= constant_expression
    { SDecl_bitfield (Option.map LF.cabs_of_declarator decltor_opt, expr) }
;

(* §6.7.2.2 Enumeration specifiers *)
enum_specifier:
| ENUM ioption(attribute_specifier_sequence) iopt= general_identifier?
  LBRACE enums= enumerator_list COMMA? RBRACE
    { TSpec (region ($startpos, $endpos) noCursor,
             TSpec_enum (iopt, Some (List.rev enums))) }
| ENUM ioption(attribute_specifier_sequence) i= general_identifier
    { TSpec (region ($startpos, $endpos) noCursor,
             TSpec_enum (Some i, None)) }
;

enumerator_list: (* NOTE: the list is in reverse *)
| enum= enumerator
    { [enum] }
| enums= enumerator_list COMMA enum= enumerator
    { enum::enums }
;

enumerator:
| enum_cst= enumeration_constant ioption(attribute_specifier_sequence)
    { (enum_cst, None) }
| enum_cst= enumeration_constant ioption(attribute_specifier_sequence)
    EQ expr= constant_expression
    { (enum_cst, Some expr) }
;

(* §6.7.2.4 Atomic type specifiers *)
atomic_type_specifier:
| ATOMIC LPAREN ty= type_name RPAREN
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_Atomic ty) }
;

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
;

attribute_type_qualifier:
  tqual= type_qualifier ioption(attribute_specifier_sequence)
    { tqual }
;

(* §6.7.4 Function specifiers *)
function_specifier:
| INLINE
    { FS_inline }
| NORETURN
    { FS_Noreturn }
;

(* §6.7.5 Alignment specifier *)
alignment_specifier:
| ALIGNAS LPAREN ty= type_name RPAREN
    { AS_type ty }
| ALIGNAS LPAREN expr= constant_expression RPAREN
    { AS_expr expr }
;

attribute_alignment_specifier:
  aspec= alignment_specifier ioption(attribute_specifier_sequence)
    { aspec }
;

(* §6.7.6 Declarators *)

(* NOTE: the declarator rules are parameterised by [ident], the identifiers
 * allowed as the identifier of the declarator, and by [paren_ident], those
 * allowed as the identifier of a parenthesised declarator. They are both
 * general_identifier, except in parameter declarations,
 * see parameter_declarator_varname. *)
declarator:
| decl= declarator_(general_identifier, general_identifier)
    { decl }
;

declarator_(ident, paren_ident):
| dd= direct_declarator(ident, paren_ident)
    { dd }
(* NOTE: after a pointer, the identifier cannot be confused with a typedef name
 * starting a parameter list *)
| pdecl= pointer dd= direct_declarator(general_identifier, paren_ident)
    { LF.pointer_decl pdecl dd }
;

direct_declarator(ident, paren_ident):
(* NOTE: using [ident] rather than [general_identifier], this is to prevent
 * a reduce/reduce conflict: in a parameter declaration, the first identifier
 * of a parenthesised declarator cannot be a typedef name, which starts the
 * parameter list of an abstract function declarator instead (STD §6.7.6.3#11),
 * see parameter_declarator_varname *)
| i = ident attr_opt= ioption(attribute_specifier_sequence)
    { LF.identifier_decl (to_attrs attr_opt) i }
| LPAREN save_context decltor= declarator_(paren_ident, paren_ident) RPAREN
    { LF.declarator_decl decltor }
| decl= array_declarator(ident, paren_ident) ioption(attribute_specifier_sequence)
| decl= function_declarator(ident, paren_ident) ioption(attribute_specifier_sequence)
    { decl }
| ddecltor= direct_declarator(ident, paren_ident) LPAREN ctxt=save_context RPAREN
    { LF.fun_decl (Params ([], false)) ctxt ddecltor }
| ddecltor= direct_declarator(ident, paren_ident) LPAREN ctxt=save_context
  rev_ids= identifier_list RPAREN
    { LF.fun_ids_decl (List.rev rev_ids) ctxt ddecltor }
;

array_declarator(ident, paren_ident):
| ddecltor= direct_declarator(ident, paren_ident) LBRACK tquals_opt= type_qualifier_list?
  expr_opt= assignment_expression? RBRACK
    { LF.array_decl (ADecl (region ($startpos, $endpos) noCursor,
        opt_to_rev_list tquals_opt, false,
        Option.map (fun x -> ADeclSize_expression x) expr_opt)) ddecltor }
| ddecltor= direct_declarator(ident, paren_ident) LBRACK STATIC tquals_opt= type_qualifier_list?
  expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (region ($startpos, $endpos) noCursor,
                            opt_to_rev_list tquals_opt,
                            true, Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator(ident, paren_ident) LBRACK tquals= type_qualifier_list STATIC
  expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (region ($startpos, $endpos) noCursor,
                            List.rev tquals, true,
                            Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator(ident, paren_ident) LBRACK tquals_opt= type_qualifier_list? STAR RBRACK
    { LF.array_decl (ADecl (region ($startpos, $endpos) noCursor,
                            opt_to_rev_list tquals_opt, false,
                            Some ADeclSize_asterisk)) ddecltor }
;

function_declarator(ident, paren_ident):
| ddecltor= direct_declarator(ident, paren_ident) LPAREN ptys_ctxt=scoped(parameter_type_list) RPAREN
    { let (ptys, ctxt) = ptys_ctxt in LF.fun_decl ptys ctxt ddecltor }
;

identifier_list: (* NOTE: the list is in reverse *)
| id= var_name
    { [ Symbol.Identifier (point $startpos, id) ] }
| ids= identifier_list COMMA id= var_name
    { Symbol.Identifier (point $startpos, id) :: ids }
;

pointer:
| STAR ioption(attribute_specifier_sequence) tquals= type_qualifier_list?
  ptr_decltor= pointer?
    { PDecl (region ($startpos, $endpos) noCursor,
             opt_to_rev_list tquals, ptr_decltor) }
;

type_qualifier_list: (* NOTE: the list is in reverse *)
| tqual= type_qualifier
    { [tqual] }
| tquals= type_qualifier_list tqual= type_qualifier
    { tqual::tquals }
;

parameter_type_list:
| param_decls= parameter_list ctxt= save_context
    { (Params (List.rev param_decls, false), ctxt) }
| param_decls= parameter_list COMMA ELLIPSIS ctxt= save_context
    { (Params (List.rev param_decls, true), ctxt)  }
;

parameter_list: (* NOTE: the list is in reverse *)
| param_decl= parameter_declaration
    { [param_decl] }
| param_decls= parameter_list COMMA param_decl= parameter_declaration
    { param_decl::param_decls }
;

parameter_declaration:
| ioption(attribute_specifier_sequence) specifs= declaration_specifiers
  decltor= parameter_declarator_varname
    { PDeclaration_decl (specifs, LF.cabs_of_declarator decltor) }
| ioption(attribute_specifier_sequence) specifs= declaration_specifiers
  abs_decltor_opt= ioption(abstract_declarator)
    { PDeclaration_abs_decl (specifs, abs_decltor_opt) }
;

(* §6.7.7 Type names *)
type_name:
| tspecs_tquals= specifier_qualifier_list abs_declr_opt= abstract_declarator?
    { let (tspecs, tquals, align_specs) = tspecs_tquals in
      Type_name (tspecs, tquals, align_specs, abs_declr_opt) }
;

abstract_declarator:
| ptr_decltor= pointer
    { AbsDecl_pointer ptr_decltor }
| ptr_decltor_opt= ioption(pointer) dabs_decltor= direct_abstract_declarator
    { AbsDecl_direct (ptr_decltor_opt, dabs_decltor) }
;

direct_abstract_declarator:
| LPAREN save_context abs_decltor= abstract_declarator RPAREN
    { DAbs_abs_declarator abs_decltor }
| dabs= array_abstract_declarator ioption(attribute_specifier_sequence)
| dabs= function_abstract_declarator ioption(attribute_specifier_sequence)
    { dabs }
;

array_abstract_declarator:
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK
  tquals= ioption(type_qualifier_list) expr= assignment_expression? RBRACK
    { DAbs_array (dabs_decltor, ADecl (region ($startpos, $endpos) noCursor,
      Option.fold ~none:[] ~some:id tquals, false,
      Option.map (fun e -> ADeclSize_expression e) expr)) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK STATIC
  tquals= type_qualifier_list? expr= assignment_expression RBRACK
    { DAbs_array (dabs_decltor, ADecl (region ($startpos, $endpos) noCursor,
      Option.fold ~none:[] ~some:id tquals, true, Some (ADeclSize_expression expr))) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK
  tquals= type_qualifier_list STATIC expr= assignment_expression RBRACK
    { DAbs_array (dabs_decltor, ADecl (region ($startpos, $endpos) noCursor, tquals, true,
      Some (ADeclSize_expression expr))) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK STAR RBRACK
    { DAbs_array (dabs_decltor, ADecl (region ($startpos, $endpos) noCursor, [], false,
      Some ADeclSize_asterisk)) }
;

function_abstract_declarator:
| dabs_decltor= ioption(direct_abstract_declarator) LPAREN
  param_tys_ctxt_opt = scoped(parameter_type_list)? RPAREN
    { match param_tys_ctxt_opt with
      | Some (param_tys, _) ->
        DAbs_function (dabs_decltor, param_tys)
      | None ->
        DAbs_function (dabs_decltor, Params ([], false)) }
;

(* §6.7.8 Type definitions *)

(* §6.7.9 Initialization *)
initializer_:
| expr= assignment_expression
    { Init_expr expr }
| LBRACE inits= initializer_list RBRACE
| LBRACE inits= initializer_list COMMA RBRACE
    { Init_list (region ($startpos, $endpos) noCursor, List.rev inits) }
;

initializer_list: (* NOTE: the list is in reverse *)
| design_opt= designation? init= initializer_
    { [(design_opt, init)] }
| inits= initializer_list COMMA design_opt= designation? init= initializer_
    { (design_opt, init)::inits }
;

designation:
| design= designator_list EQ
    { List.rev design }
;

designator_list: (* NOTE: the list is in reverse *)
| design= designator
    { [design] }
| designs= designator_list design= designator
    { design::designs }
;

designator:
| LBRACK expr= constant_expression RBRACK
    { Desig_array expr }
| DOT i= general_identifier
    { Desig_member i }
;

(* §6.7.10 Static assertions *)
static_assert_declaration:
| STATIC_ASSERT LPAREN expr= constant_expression COMMA
  lit= STRING_LITERAL RPAREN SEMICOLON
    { Static_assert (expr, lit) }
;

(* §6.8 Statements and blocks *)
statement:
| stmt= labeled_statement
    { stmt }
| attr_opt= attribute_specifier_sequence? stmt= scoped(compound_statement)
    { inject_attr attr_opt stmt }
| stmt= expression_statement
    { stmt }
| attr_opt= attribute_specifier_sequence? stmt= scoped(selection_statement)
| attr_opt= attribute_specifier_sequence? stmt= scoped(iteration_statement)
| attr_opt= attribute_specifier_sequence? stmt= jump_statement
    { inject_attr attr_opt stmt }
| stmt= asm_statement
    { stmt }
;

(* §6.8.1 Labeled statements *)
labeled_statement:
| attr_opt= ioption(attribute_specifier_sequence) i= general_identifier COLON
  stmt= statement
    { CabsStatement (region ($startpos(i), $endpos) noCursor,
        to_attrs attr_opt,
        CabsSlabel (i, stmt)) }
| attr_opt= attribute_specifier_sequence? CASE expr1= constant_expression ELLIPSIS expr2= constant_expression COLON
  stmt= statement
    { CabsStatement
        ( region ($startpos($2), $endpos) noCursor
        , to_attrs attr_opt
        , CabsScaseGNU (expr1, expr2, stmt) ) }
| attr_opt= attribute_specifier_sequence? CASE expr= constant_expression COLON
  stmt= statement
    { CabsStatement
        ( region ($startpos($2), $endpos) noCursor
        , to_attrs attr_opt
        , CabsScase (expr, stmt) ) }
| attr_opt= attribute_specifier_sequence? DEFAULT COLON stmt= statement
    { CabsStatement
        ( region ($startpos($2), $endpos) noCursor
        , to_attrs attr_opt
        , CabsSdefault stmt ) }
;

(* §6.8.2 Compound statement *)
compound_statement:
| LBRACE bis_opt= block_item_list? RBRACE
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSblock (opt_to_rev_list bis_opt) ) }
(* NON-STD cppmem syntax *)
| LBRACES stmts= separated_nonempty_list(PIPES, statement) RBRACES
    { CabsStatement (region ($startpos, $endpos) noCursor,
                     Annot.no_attributes,
                     CabsSpar stmts) }
;

block_item_list: (* NOTE: the list is in reverse *)
| stmt= block_item
    { [stmt] }
| stmts= block_item_list stmt= block_item
    { stmt::stmts }
;

block_item:
(* GNU extension: allowing __extension__ keywords to precede the declaration *)
| xs_decl= declaration_ext
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSdecl xs_decl ) }
| stmt= statement
    { stmt }
(* magic comments as statements - permitted in blocks but not at all
   other statement positions to avoid a parse conflict on
   while(1) /*@ inv X @*/ {} *)
| magic= CERB_MAGIC
    {
      let loc = fst magic in
      let null = CabsStatement ( loc, Annot.no_attributes, CabsSnull ) in
      CabsStatement
        ( loc
        , magic_to_attrs [magic]
        , CabsSmarker null ) }
;

(* §6.8.3 Expression and null statements *)
expression_statement:
| expr_opt= expression? SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , Option.fold ~none:CabsSnull ~some:(fun z -> CabsSexpr z) expr_opt ) }
| attr= attribute_specifier_sequence expr= expression SEMICOLON
    { CabsStatement
        (region ($startpos, $endpos) noCursor
        , to_attrs (Some attr)
        , CabsSexpr expr ) }
;

(* §6.8.4 Selection statements *)
selection_statement:
| IF LPAREN expr= expression RPAREN stmt= scoped(statement) %prec THEN
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSif (expr, stmt, None) ) }
| IF LPAREN expr= expression RPAREN stmt1= scoped(statement)
  ELSE stmt2= scoped(statement)
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSif (expr, stmt1, Some stmt2) ) }
| SWITCH LPAREN expr= expression RPAREN stmt= scoped(statement)
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSswitch (expr, stmt) ) }
;

(* FIXME magic comments should be singletons, not a list *)
magic_comment_list:
| xs= list(CERB_MAGIC)
    { xs }

(* §6.8.5 Iteration statements *)
iteration_statement:
| WHILE LPAREN expr= expression RPAREN magic= magic_comment_list stmt= scoped(statement)
    {
      CabsStatement
        ( region ($startpos, $endpos) noCursor
        , magic_to_attrs magic
        , CabsSwhile (expr, stmt) ) }
| DO magic= magic_comment_list stmt= scoped(statement) WHILE LPAREN expr= expression RPAREN SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , magic_to_attrs magic
        , CabsSdo (expr, stmt) ) }
| FOR LPAREN expr1_opt= expression? SEMICOLON expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN magic= magic_comment_list stmt= scoped(statement)
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , magic_to_attrs magic
        , CabsSfor (Option.map (fun x -> FC_expr x) expr1_opt, expr2_opt,expr3_opt, stmt) ) }
(* GNU extension: allowing __extension__ keywords to precede the declaration *)
| FOR LPAREN xs_decl= declaration_ext expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN magic= magic_comment_list stmt= scoped(statement)
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , magic_to_attrs magic
        , CabsSfor (Some (FC_decl (region $loc(xs_decl) noCursor, xs_decl)), expr2_opt, expr3_opt, stmt) ) }
;

(* §6.8.6 Jump statements *)
jump_statement:
| GOTO i= general_identifier SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSgoto i ) }
| CONTINUE SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsScontinue ) }
| BREAK SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSbreak ) }
| RETURN expr_opt= expression? SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSreturn expr_opt ) }
;

(* GCC extension: Extended Asm
 *   - https://gcc.gnu.org/onlinedocs/gcc/Basic-Asm.html
 *   - https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html
 *   - https://gcc.gnu.org/onlinedocs/gcc/Asm-Labels.html
 *
 * NOTE: the lexer produces a COLON_COLON token for "::" (for attributes),
 * which in an asm stands for two consecutive COLON. The grammar of sections
 * is tweaked to handle this properly (see below). *)

asm_register:
| ASM LPAREN STRING_LITERAL RPAREN
    { () }
;

asm_qualifier:
| VOLATILE
    { (region $loc noCursor, CabsAsm_volatile) }
| INLINE
    { (region $loc noCursor, CabsAsm_inline) }
| GOTO
    { (region $loc noCursor, CabsAsm_goto) }
;

asm_operand:
| name_opt= ioption(delimited(LBRACK, general_identifier, RBRACK))
  lit= STRING_LITERAL LPAREN expr= expression RPAREN
    { { cabs_asm_operand_name= name_opt
      ; cabs_asm_operand_constraint= lit
      ; cabs_asm_operand_expr= expr } }
;

asm_operands:
| ops= separated_list(COMMA, asm_operand)
    { ops }
;

asm_clobbers:
| lits= separated_list(COMMA, STRING_LITERAL)
    { lits }
;

asm_goto_labels:
| labels= separated_nonempty_list(COMMA, general_identifier)
    { labels }
;

(* The structure of grammar for the sections differs from the one in the
 * GCC documentation to properly treat a "::" token like two ':' tokens with an
 * empty section between them. *)
asm_sections:
| COLON outputs= asm_operands rest= asm_sections_inputs
    { let (inputs_opt, clobbers_opt, labels_opt) = rest in
      { cabs_asm_outputs= outputs
      ; cabs_asm_inputs= inputs_opt
      ; cabs_asm_clobbers= clobbers_opt
      ; cabs_asm_labels= labels_opt } }
| COLON_COLON rest= asm_sections_inputs_body
    { let (inputs_opt, clobbers_opt, labels_opt) = rest in
      { cabs_asm_outputs= []
      ; cabs_asm_inputs= inputs_opt
      ; cabs_asm_clobbers= clobbers_opt
      ; cabs_asm_labels= labels_opt } }
;

asm_sections_inputs:
| (* empty *)
    { (None, None, None) }
| COLON rest= asm_sections_inputs_body
    { rest }
| COLON_COLON rest= asm_sections_clobbers_body
    { let (clobbers_opt, labels_opt) = rest in
      (Some [], clobbers_opt, labels_opt) }
;

asm_sections_inputs_body:
| inputs= asm_operands rest= asm_sections_clobbers
    { let (clobbers_opt, labels_opt) = rest in
      (Some inputs, clobbers_opt, labels_opt) }
;

asm_sections_clobbers:
| (* empty *)
    { (None, None) }
| COLON rest= asm_sections_clobbers_body
    { rest }
| COLON_COLON labels= asm_goto_labels
    { (Some [], Some labels) }
;

asm_sections_clobbers_body:
| clobbers= asm_clobbers labels_opt= asm_sections_labels
    { (Some clobbers, labels_opt) }
;

asm_sections_labels:
| (* empty *)
    { None }
| COLON labels= asm_goto_labels
    { Some labels }
;

asm:
| ASM qs= asm_qualifier* LPAREN template= STRING_LITERAL sections_opt= asm_sections? RPAREN
    { { cabs_asm_qualifiers= qs
      ; cabs_asm_template= template
      ; cabs_asm_sections= sections_opt } }
;

asm_statement:
| asm= asm SEMICOLON
    { CabsStatement
        ( region ($startpos, $endpos) noCursor
        , Annot.no_attributes
        , CabsSasm asm ) }
;


(* §6.9 External definitions *)
external_declaration_list: (* NOTE: the list is in reverse *)
| def= external_declaration
    { [def] }
| defs= external_declaration_list def= external_declaration
    { def :: defs }
;

external_declaration:
| magic= CERB_MAGIC
    { EDecl_magic (fst magic, snd (snd magic)) }
| fdef= function_definition
    { EDecl_func fdef }
| xs_decl= declaration has_extra= boption(SEMICOLON+)
    { if has_extra then warn_extra_semicolon $startpos(has_extra) AFTER_EDECL;
      EDecl_decl xs_decl }
(* GCC extension: asm-definition *)
| asm= asm SEMICOLON has_extra= boption(SEMICOLON+)
    { if has_extra then warn_extra_semicolon $startpos(has_extra) AFTER_EDECL;
      EDecl_asm (region ($startpos, $endpos(asm)) noCursor, asm) }
| EXTENSION decl= external_declaration
    { decl }
;

(* §6.9.1 Function definitions *)
function_definition1:
| attr_opt= ioption(attribute_specifier_sequence) specifs= declaration_specifiers
  decltor= declarator_varname
    { let ctxt = LF.save_context () in
      LF.reinstall_function_context decltor;
      (attr_opt, specifs, decltor, ctxt) }
;

function_definition:
| specifs_decltor_ctxt= function_definition1 rev_decl_opt= declaration_list?
  magic= magic_comment_list
  stmt= compound_statement has_semi= boption(SEMICOLON)
    { if has_semi then warn_extra_semicolon $startpos(has_semi) AFTER_FUNCTION;
      let loc = region ($startpos, $endpos) noCursor in
      let (attr_opt, specifs, decltor, ctxt) = specifs_decltor_ctxt in
      let magic_opt = magic_to_opt_attrs magic in
      LF.restore_context ctxt;
      LF.create_function_definition loc attr_opt magic_opt specifs decltor stmt rev_decl_opt }
;

declaration_list: (* NOTE: the list is in reverse *)
| xs_decl= no_leading_attribute_declaration
    { [xs_decl] }
| decls= declaration_list xs_decl= no_leading_attribute_declaration
    { xs_decl :: decls }
;

(* (N2335) §6.7.11: Attributes  *)
attribute_declaration:
| rev_attr_seq= attribute_specifier_sequence SEMICOLON
    { List.rev rev_attr_seq }
;

attribute_specifier_sequence:  (* NOTE: the list is in reverse *)
| attrs=attribute_specifier
    { [ attrs ] }
| attr_seq=attribute_specifier_sequence attrs=attribute_specifier
    { attrs :: attr_seq }
;

attribute_specifier:
| LBRACK_LBRACK attrs= attribute_list RBRACK RBRACK
    { List.rev attrs }
;

attribute_list: (* NOTE: the list is in reverse *)
| attr= attribute
    { [attr] }
| attrs= attribute_list COMMA attr= attribute
    { attr::attrs }
;

attribute:
| attr= attribute_token args_opt= attribute_argument_clause?
    { (attr, args_opt) }
;

(* C keywords are allowed to appear as attribute identifiers *)
(* TODO: there probably is a better way of doing this... *)
c_keyword_as_string:
| AUTO
    { "auto" }
| BREAK
    { "break" }
| CASE
    { "case" }
| CHAR
    { "char" }
| CONST
    { "const" }
| CONTINUE
    { "continue" }
| DEFAULT
    { "default" }
| DO
    { "do" }
| DOUBLE
    { "double" }
| ELSE
    { "else" }
| ENUM
    { "enum" }
| EXTERN
    { "extern" }
| FLOAT
    { "float" }
| FOR
    { "for" }
| GOTO
    { "goto" }
| IF
    { "if" }
| INLINE
    { "inline" }
| INT
    { "int" }
| LONG
    { "long" }
| REGISTER
    { "register" }
| RESTRICT
    { "restrict" }
| RETURN
    { "return" }
| SHORT
    { "short" }
| SIGNED
    { "signed" }
| SIZEOF
    { "sizeof" }
| STATIC
    { "static" }
| STRUCT
    { "struct" }
| SWITCH
    { "switch" }
| TYPEDEF
    { "typedef" }
| UNION
    { "union" }
| UNSIGNED
    { "unsigned" }
| VOID
    { "void" }
| VOLATILE
    { "volatile" }
| WHILE
    { "while" }
| ALIGNAS
    { "_Alignas" }
| ALIGNOF
    { "_Alignof" }
| ATOMIC
    { "_Atomic" }
| BOOL
    { "_Bool" }
| COMPLEX
    { "_Complex" }
| GENERIC
    { "_Generic" }
(* IMAGINARY *)
| NORETURN
    { "_Noreturn" }
| STATIC_ASSERT
    { "_Static_assert" }
| THREAD_LOCAL
    { "_Thread_local" }

attribute_identifier:
| name= general_identifier
    { name }
| str= c_keyword_as_string
    { Symbol.Identifier (point $startpos, str) }

attribute_token:
| name= attribute_identifier
    { (None, name) }
| attr= attribute_prefixed_token
    { attr }
;

attribute_prefixed_token:
| pre= attribute_identifier COLON_COLON name= attribute_identifier
    { (Some pre, name) }
;

attribute_argument_clause:
| LPAREN attr_args= balanced_token_sequence RPAREN
    { List.concat (List.rev attr_args) }
;

balanced_token_sequence: (* NOTE: the list is in reverse *)
| tk= balanced_token
    { [tk] }
| tks= balanced_token_sequence tk= balanced_token
    { tk :: tks }
;

located_string_literal:
| STRING_LITERAL
    { let loc = region ($startpos, $endpos) noCursor in
      let strs = List.map (fun (loc, s) -> (loc, String.concat "" s)) (snd $1) in
      (loc, String.concat "" (List.map snd strs), strs) }
;

balanced_token:
| LPAREN balanced_token_sequence RPAREN
| LBRACK balanced_token_sequence RBRACK
| LBRACE balanced_token_sequence RBRACE
    { [] }
(* NOTE: add attribute arguments here *)
| strs= separated_nonempty_list(COMMA, located_string_literal)
   { strs }
;
