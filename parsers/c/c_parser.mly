(* Grammar based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11"

   NOTE: There is a reduce/reduce conflict in the grammar, which is solved
         by reducing to the first production (Menhir's default behaviour).
         See Jourdan's paper.
*)

%{
open Cerb_frontend

open Cabs
open Cn

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
  ; attr_args= List.map (fun (loc, str) -> (loc, str, [loc, str])) magik }

let magic_to_attrs = function
  | [] ->
      Annot.Attrs []
  | magic ->
      Annot.Attrs [magic_to_attr magic]

let magic_to_opt_attrs = function
  | [] -> None
  | magic -> Some (magic_to_attrs magic)

let append_magic loc magic stmt =
  match magic with
    | [] -> stmt
    | _  -> (* let loc = Location_ocaml.bbox_location (List.map fst magic) in *)
            CabsStatement (loc, magic_to_attrs magic, CabsSmarker stmt)

let mk_statement magic (loc, attrs, stmt_) =
  append_magic loc magic (CabsStatement (loc, attrs, stmt_))

(* use this to show a warning when a NON-STD 'extra' semicolon was parsed *)
let warn_extra_semicolon pos ctx =
  if not (Cerb_global.isPermissive ()) then
    prerr_endline (Pp_errors.make_message
                    (Cerb_location.point pos)
                    Errors.(CPARSER (Cparser_extra_semi ctx))
                    Warning)
  else
    ()

type asm_qualifier =
  | ASM_VOLATILE
  | ASM_INLINE
  | ASM_GOTO
%}

(* §6.4.1 keywords *)
%token AUTO (*BREAK CASE*) CHAR CONST (*CONTINUE DEFAULT DO*) DOUBLE ELSE ENUM EXTERN
  FLOAT (*FOR GOTO IF*) INLINE INT LONG REGISTER RESTRICT (*RETURN*) SHORT SIGNED SIZEOF
  STATIC STRUCT (*SWITCH*) TYPEDEF UNION UNSIGNED VOID VOLATILE (*WHILE*) ALIGNAS
  ALIGNOF ATOMIC BOOL COMPLEX GENERIC (* IMAGINARY *) NORETURN STATIC_ASSERT
  THREAD_LOCAL
%token BREAK CASE CONTINUE DEFAULT DO FOR GOTO IF RETURN SWITCH WHILE

(* §6.4.2 Identifiers *)
%token<string> UNAME (* Uppercase. UNAME is either a variable identifier or a type name *)
%token<string> LNAME (* Lowercase. LNAME is either a variable identifier or a type name *)
%token VARIABLE TYPE

(* §6.4.4 Constants *)
%token<Cabs.cabs_constant> CONSTANT

(* §6.4.5 String literals *)
%token<Cabs.cabs_encoding_prefix option * string list> STRING_LITERAL

(* §6.4.6 Punctuators *)
%token LBRACK RBRACK LPAREN RPAREN (*LBRACE RBRACE*) DOT MINUS_GT
  PLUS_PLUS MINUS_MINUS AMPERSAND STAR PLUS MINUS TILDE BANG
  SLASH PERCENT LT_LT GT_GT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET PIPE
  AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON (*SEMICOLON*) ELLIPSIS EQ STAR_EQ SLASH_EQ PERCENT_EQ COLON_COLON
  PLUS_EQ MINUS_EQ LT_LT_EQ GT_GT_EQ AMPERSAND_EQ CARET_EQ PIPE_EQ COMMA
  LBRACK_LBRACK (*RBRACK_RBRACK*)
%token LBRACE RBRACE SEMICOLON

(* NON-STD: *)
  ASSERT OFFSETOF TYPEOF QUESTION_COLON BUILTIN_TYPES_COMPATIBLE_P BUILTIN_CHOOSE_EXPR

(* NON-STD cppmem syntax *)
  LBRACES PIPES RBRACES

%token VA_START VA_COPY VA_ARG VA_END PRINT_TYPE ASM ASM_VOLATILE

(* BMC syntax *)
%token BMC_ASSUME

(* magic comment token *)
%token<Cerb_location.t * string> CERB_MAGIC

(* CN syntax *)
(* %token<string> CN_PREDNAME *)
%token CN_ACCESSES CN_TRUSTED CN_REQUIRES CN_ENSURES CN_INV
%token CN_PACK CN_UNPACK CN_HAVE CN_EXTRACT CN_INSTANTIATE CN_SPLIT_CASE CN_UNFOLD CN_APPLY CN_PRINT
%token CN_BOOL CN_INTEGER CN_REAL CN_POINTER CN_ALLOC_ID CN_MAP CN_LIST CN_TUPLE CN_SET
%token <[`U|`I] * int>CN_BITS
%token CN_LET CN_TAKE CN_OWNED CN_BLOCK CN_EACH CN_FUNCTION CN_LEMMA CN_PREDICATE
%token CN_DATATYPE CN_TYPE_SYNONYM CN_SPEC CN_ARRAY_SHIFT CN_MEMBER_SHIFT
%token CN_UNCHANGED CN_WILD CN_MATCH
%token CN_GOOD CN_NULL CN_TRUE CN_FALSE
%token <string * [`U|`I] * int> CN_CONSTANT

%token EOF

%nonassoc THEN
%nonassoc ELSE


(* ========================================================================== *)

%type<string> typedef_name var_name
%type<Symbol.identifier> general_identifier

%type<LF.context> save_context

%type<LF.declarator> declarator direct_declarator declarator_varname
  declarator_typedefname

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

%type<Cabs.specifiers>
  declaration_specifiers

%type<Cabs.storage_class_specifier>
  storage_class_specifier

%type<Cabs.cabs_type_specifier>
  struct_or_union_specifier

%type<Annot.attributes -> Symbol.identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier>
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

%type<Cabs.cabs_encoding_prefix option * (Cerb_location.t * string list)>
  string_literal_component

%type<Cabs.cabs_string_literal>
  string_literal

%type<Cerb_location.t * string * (Cerb_location.t * string) list>
  located_string_literal

%start<Cerb_frontend.Cabs.translation_unit> translation_unit
%start function_spec
%start loop_spec
%start cn_statements
%start cn_toplevel

%type<Symbol.identifier Cn.cn_base_type> base_type
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_function> cn_function
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_predicate> cn_predicate
%type<(Symbol.identifier) Cn.cn_datatype> cn_datatype
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_clauses> clauses
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_clause> clause
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_resource> resource
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_pred> pred
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_condition> condition
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_function_spec list> function_spec
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_loop_spec> loop_spec
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_statement> cn_statement
%type<((Symbol.identifier, Cabs.type_name) Cn.cn_statement) list> cn_statements
%type<(Symbol.identifier * Symbol.identifier Cn.cn_base_type) list> cn_args


%type<Cabs.external_declaration> cn_toplevel_elem
%type<Cabs.external_declaration list> cn_toplevel



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

%inline NAME:
| u= UNAME
    { u }
| l= LNAME
    { l }


typedef_name:
| n= NAME TYPE
    { n }
;

var_name:
| n= NAME VARIABLE
    { n }
;

(* NOTE: This rule is declared early, so that reduce/reduce conflict is
   resolved using it. *)
typedef_name_spec:
| i= typedef_name
    { TSpec ((Cerb_location.(region ($startpos, $endpos) NoCursor)),
             TSpec_name (Identifier (Cerb_location.point $startpos, i))) }
;

general_identifier:
| i= typedef_name
| i= var_name
    { Symbol.Identifier (Cerb_location.(region ($startpos, $endpos) NoCursor), i) }
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

(* §6.4.4.3 Enumeration constants Primary expressions *)
enumeration_constant:
| i= general_identifier
    { LF.declare_varname (string_of_cabs_id i); i }
;

(* §6.5.1 Primary expressions *)
primary_expression:
| str= var_name
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
        CabsEident (Symbol.Identifier (Cerb_location.point $startpos(str), str))) }
| cst= CONSTANT
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
                      CabsEconst cst) }
| lit= string_literal
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
                      CabsEstring lit) }
| LPAREN expr= expression RPAREN
    { let CabsExpression (_, expr_) = expr in
      CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor), expr_ ) }
| gs= generic_selection
    { gs }
(* GCC extension: Statement Exprs *)
// | LPAREN stmt= scoped(compound_statement) RPAREN
| LPAREN LBRACE bis_opt= block_item_list? RBRACE RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEgcc_statement (option [] List.rev bis_opt) ) }
;

(* §6.5.1.1 Generic selection *)
generic_selection:
| GENERIC LPAREN expr= assignment_expression COMMA gas= generic_assoc_list RPAREN
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                     , CabsEsubscript (expr1, expr2) ) }
| expr= postfix_expression LPAREN exprs_opt= argument_expression_list? RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                     , CabsEcall (expr, option [] List.rev exprs_opt) ) }
| expr= postfix_expression DOT i= general_identifier
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEmemberof (expr, i) ) }
| expr= postfix_expression MINUS_GT i= general_identifier
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEmemberofptr (expr, i) ) }
| expr= postfix_expression PLUS_PLUS
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEpostincr expr ) }
| expr= postfix_expression MINUS_MINUS
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEpostdecr expr ) }
| LPAREN ty= type_name RPAREN LBRACE inits= initializer_list COMMA? RBRACE
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
                      CabsEcompound (ty, List.rev inits)) }
(* NOTE: non-std way of dealing with these *)
| ASSERT LPAREN expr= assignment_expression RPAREN
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
                      CabsEassert expr) }
| VA_START LPAREN expr= assignment_expression COMMA i= general_identifier RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEva_start(expr, i) ) }
| VA_COPY LPAREN e1= assignment_expression COMMA e2= assignment_expression RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEva_copy(e1, e2) ) }
| VA_ARG LPAREN expr= assignment_expression COMMA ty= type_name RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEva_arg(expr, ty) ) }
| VA_END LPAREN expr= assignment_expression RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEva_end(expr) ) }
| OFFSETOF LPAREN ty= type_name COMMA i= general_identifier RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                     , CabsEoffsetof (ty, i) ) }
| BUILTIN_TYPES_COMPATIBLE_P LPAREN ty1= type_name COMMA ty2= type_name RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                     , CabsEbuiltinGNU (GNUbuiltin_types_compatible_p (ty1, ty2)) ) }
| BUILTIN_CHOOSE_EXPR LPAREN const_e= assignment_expression COMMA e1= assignment_expression COMMA e2= assignment_expression RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                     , CabsEbuiltinGNU (GNUbuiltin_choose_expr (const_e, e1, e2)) ) }
(* NOTE: the following is a cerb extension allowing the user to the
   query the type of an expression  *)
| PRINT_TYPE LPAREN expr= expression RPAREN
   { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
        CabsEprint_type expr) }
| BMC_ASSUME LPAREN expr= assignment_expression RPAREN
    { CabsExpression (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
    { CabsExpression ( Cerb_location.region ($startpos, $endpos) (PointCursor $startpos($1))
                     , CabsEpreincr expr ) }
| MINUS_MINUS expr= unary_expression
    { CabsExpression ( Cerb_location.region ($startpos, $endpos) (PointCursor $startpos($1))
                     , CabsEpredecr expr ) }
| op= unary_operator expr= cast_expression
    { CabsExpression ( Cerb_location.region ($startpos, $endpos) (PointCursor $startpos(op))
                     , CabsEunary (op, expr) ) }
| SIZEOF expr= unary_expression
    { CabsExpression ( Cerb_location.region ($startpos, $endpos) (PointCursor $startpos($1))
                     , CabsEsizeof_expr expr ) }
| SIZEOF LPAREN ty= type_name RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                     , CabsEsizeof_type ty ) }
| ALIGNOF LPAREN ty= type_name RPAREN
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                     , CabsEalignof ty ) }
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
    { CabsExpression ( Cerb_location.region ($startpos, $endpos) (PointCursor $startpos($1))
                     , CabsEcast (ty, expr) ) }
;

(* §6.5.5 Multiplicative operators *)
multiplicative_expression:
| expr= cast_expression
    { expr }
| expr1= multiplicative_expression STAR expr2= cast_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsMul, expr1, expr2) ) }
| expr1= multiplicative_expression SLASH expr2= cast_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsDiv, expr1, expr2) ) }
| expr1= multiplicative_expression PERCENT expr2= cast_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsMod, expr1, expr2) ) }
;

(* §6.5.6 Additive operators *)
additive_expression:
| expr= multiplicative_expression
    { expr }
| expr1= additive_expression PLUS expr2= multiplicative_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsAdd, expr1, expr2) ) }
| expr1= additive_expression MINUS expr2= multiplicative_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsSub, expr1, expr2) ) }
;

(* §6.5.7 Bitwise shift operators *)
shift_expression:
| expr= additive_expression
    { expr }
| expr1= shift_expression LT_LT expr2= additive_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsShl, expr1, expr2) ) }
| expr1= shift_expression GT_GT expr2= additive_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsShr, expr1, expr2) ) }
;

(* §6.5.8 Relational operators *)
relational_expression:
| expr= shift_expression
    { expr }
| expr1= relational_expression LT expr2= shift_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsLt, expr1, expr2) ) }
| expr1= relational_expression GT expr2= shift_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsGt, expr1, expr2) ) }
| expr1= relational_expression LT_EQ expr2= shift_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsLe, expr1, expr2) ) }
| expr1= relational_expression GT_EQ expr2= shift_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsGe, expr1, expr2) ) }
;

(* §6.5.9 Equality operators *)
equality_expression:
| expr= relational_expression
    { expr }
| expr1= equality_expression EQ_EQ expr2= relational_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsEq, expr1, expr2) ) }
| expr1= equality_expression BANG_EQ expr2= relational_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsNe, expr1, expr2) ) }
;

(* §6.5.10 Bitwise AND operator *)
_AND_expression:
| expr= equality_expression
    { expr }
| expr1= _AND_expression AMPERSAND expr2= equality_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsBand, expr1, expr2) ) }
;

(* §6.5.11 Bitwise exclusive OR operator *)
exclusive_OR_expression:
| expr= _AND_expression
    { expr }
| expr1= exclusive_OR_expression CARET expr2= _AND_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsBxor, expr1, expr2) ) }
;

(* §6.5.12 Bitwise inclusive OR operator *)
inclusive_OR_expression:
| expr= exclusive_OR_expression
    { expr }
| expr1= inclusive_OR_expression PIPE expr2= exclusive_OR_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsBor, expr1, expr2) ) }
;

(* §6.5.13 Logical AND operator *)
logical_AND_expression:
| expr= inclusive_OR_expression
    { expr }
| expr1=logical_AND_expression AMPERSAND_AMPERSAND expr2=inclusive_OR_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsAnd, expr1, expr2) ) }
;

(* §6.5.14 Logical OR operator *)
logical_OR_expression:
| expr= logical_AND_expression
    { expr }
| expr1= logical_OR_expression PIPE_PIPE expr2= logical_AND_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEbinary (CabsOr, expr1, expr2) ) }
;

(* §6.5.15 Conditional operator *)
conditional_expression:
| expr= logical_OR_expression
    { expr }
| expr1= logical_OR_expression QUESTION expr2= expression
                               COLON    expr3= conditional_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEcond (expr1, expr2, expr3) ) }
| expr1= logical_OR_expression QUESTION_COLON expr2= conditional_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                     , CabsEcondGNU (expr1, expr2) ) }
;

(* §6.5.16 Assignment operators *)
assignment_expression:
| expr= conditional_expression
    { expr }
| expr1= unary_expression op= assignment_operator expr2= assignment_expression
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos(op)))
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
    { CabsExpression ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
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
    { Declaration_base (Annot.no_attributes, decspecs, option [] List.rev idecls_opt) }
| decspecs= declaration_specifiers_typedef
    idecls_opt= init_declarator_list(declarator_typedefname)? SEMICOLON
    { Declaration_base (Annot.no_attributes, decspecs, option [] List.rev idecls_opt) }
| sa= static_assert_declaration
    { Declaration_static_assert sa }
;

declaration:
| xs_decl= no_leading_attribute_declaration
    { xs_decl }
| attr= attribute_specifier_sequence decspecs= declaration_specifiers
    idecls_opt= init_declarator_list(declarator_varname)? SEMICOLON
    { Declaration_base (to_attrs (Some attr), decspecs, option [] List.rev idecls_opt) }
| attr= attribute_specifier_sequence decspecs= declaration_specifiers_typedef
    idecls_opt= init_declarator_list(declarator_typedefname)? SEMICOLON
    { Declaration_base (to_attrs (Some attr), decspecs, option [] List.rev idecls_opt) }
| attribute_declaration
    { (*TODO: this is a dummy declaration*)
      let loc = Cerb_location.(region($startpos, $endpos) (PointCursor $startpos)) in
      Declaration_base (Annot.no_attributes, empty_specs, [InitDecl (loc, Declarator (None, DDecl_identifier (Annot.no_attributes, Symbol.Identifier (loc, "test"))), None)]) }
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
    { InitDecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
                LF.cabs_of_declarator decl, None) }
| decl= declarator ioption(asm_register) EQ init= initializer_
    { InitDecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_char) }
| SHORT
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_short) }
| INT
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_int) }
| LONG
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_long) }
| FLOAT
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_float) }
| DOUBLE
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_double) }
| SIGNED
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_signed) }
| UNSIGNED
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_unsigned) }
| COMPLEX
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_Complex) }
;

attribute_type_specifier_nonunique:
| ty= type_specifier_nonunique ioption(attribute_specifier_sequence)
    { ty }
;

type_specifier_unique:
| VOID
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_void) }
| BOOL
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_Bool) }
| spec= atomic_type_specifier
    { spec }
| spec= struct_or_union_specifier
    { spec }
| spec= enum_specifier
    { spec }
| spec= typedef_name_spec
    { spec }
| TYPEOF LPAREN expr= expression RPAREN
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_typeof_expr expr) }
| TYPEOF LPAREN ty= type_name RPAREN
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_typeof_type ty) }
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
      ctor (to_attrs attr_opt) iopt (Some (List.rev rev_decls)) }
| ctor= struct_or_union attr_opt= attribute_specifier_sequence?
    i= general_identifier
    { ctor (to_attrs attr_opt) (Some i) None }
| ctor= struct_or_union attr_opt= attribute_specifier_sequence?
    iopt= general_identifier? LBRACE RBRACE
    (* GCC extension *)
    (* TODO: forbid union *)
    { ctor (to_attrs attr_opt) iopt (Some []) }
;

struct_or_union:
| STRUCT
    { fun attrs x y -> TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor),
                              TSpec_struct (attrs, x, y)) }
| UNION
    { fun attrs x y -> TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
                          option [] List.rev rev_sdeclrs_opt) }
| sa_decl= static_assert_declaration
    { Struct_assert sa_decl }
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
    { SDecl_bitfield (map_option LF.cabs_of_declarator decltor_opt, expr) }
;

(* §6.7.2.2 Enumeration specifiers *)
enum_specifier:
| ENUM ioption(attribute_specifier_sequence) iopt= general_identifier?
  LBRACE enums= enumerator_list COMMA? RBRACE
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor),
             TSpec_enum (iopt, Some (List.rev enums))) }
| ENUM ioption(attribute_specifier_sequence) i= general_identifier
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
    { TSpec (Cerb_location.(region ($startpos, $endpos) NoCursor), TSpec_Atomic ty) }
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

declarator:
| dd= direct_declarator
    { dd }
| pdecl= pointer dd= direct_declarator
    { LF.pointer_decl pdecl dd }
;

direct_declarator:
| i = general_identifier attr_opt= ioption(attribute_specifier_sequence) (* TODO/FIXME: this introduce a reduce/reduce conflict *)
    { LF.identifier_decl (to_attrs attr_opt) i }
| LPAREN save_context decltor= declarator RPAREN
    { LF.declarator_decl decltor }
| decl= array_declarator ioption(attribute_specifier_sequence)
| decl= function_declarator ioption(attribute_specifier_sequence)
    { decl }
| ddecltor= direct_declarator LPAREN ctxt=save_context RPAREN
    { LF.fun_decl (Params ([], false)) ctxt ddecltor }
| ddecltor= direct_declarator LPAREN ctxt=save_context
  rev_ids= identifier_list RPAREN
    { LF.fun_ids_decl (List.rev rev_ids) ctxt ddecltor }
;

array_declarator:
| ddecltor= direct_declarator LBRACK tquals_opt= type_qualifier_list?
  expr_opt= assignment_expression? RBRACK
    { LF.array_decl (ADecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
        option [] List.rev tquals_opt, false,
        map_option (fun x -> ADeclSize_expression x) expr_opt)) ddecltor }
| ddecltor= direct_declarator LBRACK STATIC tquals_opt= type_qualifier_list?
  expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
                            option [] List.rev tquals_opt,
                            true, Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator LBRACK tquals= type_qualifier_list STATIC
  expr= assignment_expression RBRACK
    { LF.array_decl (ADecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
                            List.rev tquals, true,
                            Some (ADeclSize_expression expr))) ddecltor }
| ddecltor= direct_declarator LBRACK tquals_opt= type_qualifier_list? STAR RBRACK
    { LF.array_decl (ADecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
                            option [] List.rev tquals_opt, false,
                            Some ADeclSize_asterisk)) ddecltor }
;

function_declarator:
| ddecltor= direct_declarator LPAREN ptys_ctxt=scoped(parameter_type_list) RPAREN
    { let (ptys, ctxt) = ptys_ctxt in LF.fun_decl ptys ctxt ddecltor }
;

identifier_list: (* NOTE: the list is in reverse *)
| id= var_name
    { [ Symbol.Identifier (Cerb_location.point $startpos, id) ] }
| ids= identifier_list COMMA id= var_name
    { Symbol.Identifier (Cerb_location.point $startpos, id) :: ids }
;

pointer:
| STAR ioption(attribute_specifier_sequence) tquals= type_qualifier_list?
  ptr_decltor= pointer?
    { PDecl (Cerb_location.(region ($startpos, $endpos) NoCursor),
             option [] List.rev tquals, ptr_decltor) }
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
  decltor= declarator_varname
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
    { DAbs_array (dabs_decltor, ADecl (Cerb_location.unknown,
      option [] id tquals, false,
      option None (fun e -> Some (ADeclSize_expression e)) expr)) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK STATIC
  tquals= type_qualifier_list? expr= assignment_expression RBRACK
    { DAbs_array (dabs_decltor, ADecl (Cerb_location.unknown,
      option [] id tquals, true, Some (ADeclSize_expression expr))) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK
  tquals= type_qualifier_list STATIC expr= assignment_expression RBRACK
    { DAbs_array (dabs_decltor, ADecl (Cerb_location.unknown, tquals, true,
      Some (ADeclSize_expression expr))) }
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK STAR RBRACK
    { DAbs_array (dabs_decltor, ADecl (Cerb_location.unknown, [], false,
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
    { Init_list (Cerb_location.(region ($startpos, $endpos) NoCursor), List.rev inits) }
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
  lit= string_literal RPAREN SEMICOLON
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
    { CabsStatement (Cerb_location.(region ($startpos, $endpos) NoCursor),
        to_attrs attr_opt,
        CabsSlabel (i, stmt)) }
| attr_opt= attribute_specifier_sequence? CASE expr1= constant_expression ELLIPSIS expr2= constant_expression COLON
  stmt= statement
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , to_attrs attr_opt
        , CabsScaseGNU (expr1, expr2, stmt) ) }
| attr_opt= attribute_specifier_sequence? CASE expr= constant_expression COLON
  stmt= statement
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , to_attrs attr_opt
        , CabsScase (expr, stmt) ) }
| attr_opt= attribute_specifier_sequence? DEFAULT COLON stmt= statement
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , to_attrs attr_opt
        , CabsSdefault stmt ) }
;

(* §6.8.2 Compound statement *)
compound_statement:
| LBRACE bis_opt= block_item_list? RBRACE
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSblock (option [] List.rev bis_opt) ) }
(* NON-STD cppmem syntax *)
| LBRACES stmts= separated_nonempty_list(PIPES, statement) RBRACES
    { CabsStatement (Cerb_location.(region ($startpos, $endpos) NoCursor),
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
| xs_decl= declaration
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
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
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , option CabsSnull (fun z -> CabsSexpr z) expr_opt ) }
| attr= attribute_specifier_sequence expr= expression SEMICOLON
    { CabsStatement
        (Cerb_location.(region ($startpos, $endpos) NoCursor)
        , to_attrs (Some attr)
        , CabsSexpr expr ) }
;

(* §6.8.4 Selection statements *)
selection_statement:
| IF LPAREN expr= expression RPAREN stmt= scoped(statement) %prec THEN
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSif (expr, stmt, None) ) }
| IF LPAREN expr= expression RPAREN stmt1= scoped(statement)
  ELSE stmt2= scoped(statement)
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSif (expr, stmt1, Some stmt2) ) }
| SWITCH LPAREN expr= expression RPAREN stmt= scoped(statement)
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSswitch (expr, stmt) ) }
;

magic_comment_list:
| xs= magic_comment_list magic= CERB_MAGIC
    { magic :: xs }
|
    { [] }

(* §6.8.5 Iteration statements *)
iteration_statement:
| WHILE LPAREN expr= expression RPAREN magic= magic_comment_list stmt= scoped(statement)
    {
      CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , magic_to_attrs (List.rev magic)
        , CabsSwhile (expr, stmt) ) }
| DO stmt= scoped(statement) WHILE LPAREN expr= expression RPAREN SEMICOLON
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSdo (expr, stmt) ) }
| FOR LPAREN expr1_opt= expression? SEMICOLON expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN magic= magic_comment_list stmt= scoped(statement)
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , magic_to_attrs (List.rev magic)
        , CabsSfor (map_option (fun x -> FC_expr x) expr1_opt, expr2_opt,expr3_opt, stmt) ) }
| FOR LPAREN xs_decl= declaration expr2_opt= expression? SEMICOLON
  expr3_opt= expression? RPAREN magic= magic_comment_list stmt= scoped(statement)
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , magic_to_attrs(List.rev magic)
        , CabsSfor (Some (FC_decl xs_decl), expr2_opt, expr3_opt, stmt) ) }
;

(* §6.8.6 Jump statements *)
jump_statement:
| GOTO i= general_identifier SEMICOLON
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSgoto i ) }
| CONTINUE SEMICOLON
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsScontinue ) }
| BREAK SEMICOLON
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSbreak ) }
| RETURN expr_opt= expression? SEMICOLON
    { CabsStatement
        ( Cerb_location.(region ($startpos, $endpos) NoCursor)
        , Annot.no_attributes
        , CabsSreturn expr_opt ) }
;

(* GCC inline assembly extension *)
asm_register:
| ASM LPAREN string_literal RPAREN
    { () }

asm_qualifier:
| VOLATILE
| ASM_VOLATILE
    { ASM_VOLATILE }
| INLINE
    { ASM_INLINE }
| GOTO
    { ASM_GOTO }
;

asm_output_input:
|                             string_literal LPAREN expression RPAREN
| LBRACK NAME VARIABLE RBRACK string_literal LPAREN expression RPAREN
    { () }

asm_clobber:
| string_literal
    { () }

asm_label:
| NAME VARIABLE
    { () }

asm_with_output:
| COLON xs= separated_list(COMMA, asm_output_input) _ys= asm_with_input?
    { let (ys, zs, ws) = match _ys with
        | None ->
            ([], [], [])
        | Some z ->
            z in
      (xs, ys, zs, ws) }

asm_with_input:
| COLON xs= separated_list(COMMA, asm_output_input) _ys= asm_with_clobbers?
    { let (ys, zs) = match _ys with
        | None ->
            ([], [])
        | Some z ->
            z in
      (xs, ys, zs) }

asm_with_clobbers:
| COLON xs= separated_list(COMMA, asm_clobber) _ys= asm_with_labels?
    { let ys = match _ys with
        | None ->
            []
        | Some z ->
            z in
      (xs, ys) }

asm_with_labels:
| COLON xs= asm_label*
    { xs }

asm_statement:
| ASM qs= asm_qualifier* LPAREN s= string_literal RPAREN
    { let is_volatile = List.mem ASM_VOLATILE qs in
      let is_inline = List.mem ASM_INLINE qs in
      let strs =
        if fst s = None then snd s else
          (* TODO: better error *)
          failwith "encoding prefix found inside a __asm__ ()"
      in
      CabsStatement (Cerb_location.(region ($startpos, $endpos) NoCursor), Annot.no_attributes,
        CabsSasm (is_volatile, is_inline, strs)) }
| ASM qs= asm_qualifier* LPAREN s= string_literal args= asm_with_output RPAREN
    { let is_volatile = List.mem ASM_VOLATILE qs in
      let is_inline = List.mem ASM_INLINE qs in
      let strs =
        if fst s = None then snd s else
          (* TODO: better error *)
          failwith "encoding prefix found inside a __asm__ ()"
      in
(*      let (outputs, inputs, clobbers, labels) = args in *)
      CabsStatement (Cerb_location.(region ($startpos, $endpos) NoCursor), Annot.no_attributes,
        CabsSasm (is_volatile, is_inline, strs(*, outputs, intputs, clobbers, labels*))) }
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
    { EDecl_magic magic }
| fdef= function_definition
    { EDecl_func fdef }
| xs_decl= declaration
    { EDecl_decl xs_decl }
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
      let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      let (attr_opt, specifs, decltor, ctxt) = specifs_decltor_ctxt in
      let magic_opt = magic_to_opt_attrs (List.rev magic) in
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
    { Symbol.Identifier (Cerb_location.point $startpos, str) }

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

string_literal_component:
| STRING_LITERAL
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      (fst $1, (loc, snd $1)) }
;

string_literal:
| string_literal_component+
    { let (pref_opts, components) = List.split $1 in
      (* Check that the encoding prefixes are not inconsistent. *)
      let rec merge_prefix pref_opt ls =
        match (pref_opt, ls) with
        | (_         , []              ) -> pref_opt
        | (_         , None       :: ls) -> merge_prefix pref_opt ls
        | (None      , pref_opt   :: ls) -> merge_prefix pref_opt ls
        | (Some pref1, Some pref2 :: ls) ->
            if pref1 = pref2 then merge_prefix pref_opt ls else
              raise (C_lexer.Error Errors.Cparser_non_standard_string_concatenation)
      in
      (merge_prefix None pref_opts, components) }
;

located_string_literal:
| string_literal
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
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

(* BEGIN CN *)
(* CN assertion language *****************************************************)
(*
cn_assertion:

    | Addr of string
        | Var of string
    | Pointee of term
        | PredOutput of string * string
    | Member of term * Id.t
    | Bool of bool
    | Integer of Z.t
        | Addition of term * term
    | Subtraction of term * term
    | Multiplication of term * term
    | Division of term * term
    | Exponentiation of term * term
    | Remainder of term * term
        | Equality of term * term
    | Inequality of term * term
    | FlipBit of {bit : term; t : term}
    | ITE of term * term * term
    | Or of term * term
    | And of term * term
    | Not of term
    | LessThan of term * term
    | LessOrEqual of term * term
    | GreaterThan of term * term
    | GreaterOrEqual of term * term
    | IntegerToPointerCast of term
    | PointerToIntegerCast of term
        | Null
    | OffsetOf of {tag:string; member:string}
    | CellPointer of (term * term) * (term * term) * term
    | Disjoint of (term * term) * (term * term)
    | App of term * term
    | Env of term * string
*)

prim_expr:
| CN_NULL
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_const CNConst_NULL)) }
| CN_TRUE
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_const (CNConst_bool true))) }
| CN_FALSE
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_const (CNConst_bool false))) }
| cst= CONSTANT
    {
      match cst with
        | Cabs.CabsInteger_const (str, None) ->
            let v = Z.of_string str in
            Cerb_frontend.Cn.(CNExpr ( Cerb_location.point $startpos
                                     , CNExpr_const (CNConst_integer v) ))
        | _ ->
            raise (C_lexer.Error (Cparser_unexpected_token "TODO cn integer const"))
    }
| cst= CN_CONSTANT
    {
        let (str,sign,n) = cst in
        let sign = match sign with
         | `U -> Cerb_frontend.Cn.CN_unsigned
         | `I -> Cerb_frontend.Cn.CN_signed in
         let v = Z.of_string str in
         Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_const (CNConst_bits ((sign,n),v))))
    }
| ident= cn_variable
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_var ident)) }
(* | ident= cn_variable DOT ident_membr= cn_variable *)
| RETURN
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos,
        CNExpr_var (Symbol.Identifier (Cerb_location.point $startpos($1), "return")))) }
| e= prim_expr DOT member=cn_variable
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_memberof (e, member))) }
| e= delimited(LPAREN, expr, RPAREN)
    { e }
| CN_ARRAY_SHIFT LT ty=ctype GT LPAREN base=expr COMMA index=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_array_shift (base, Some ty, index))) }
| CN_ARRAY_SHIFT LPAREN base=expr COMMA index=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_array_shift (base, None, index))) }
| CN_MEMBER_SHIFT LPAREN base=expr COMMA member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_membershift (base, None, member))) }
| CN_MEMBER_SHIFT LT tag=cn_variable GT LPAREN base=expr COMMA member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_membershift (base, Some tag, member))) }
| ident= cn_variable LPAREN args=separated_list(COMMA, expr) RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_call (ident, args))) }
| ct= cn_good LPAREN arg=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_good (ct, arg))) }
| ident= cn_variable args= cons_args
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos(args)))
                               , CNExpr_cons (ident, args))) }
| arr= prim_expr LBRACK idx= expr RBRACK
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_map_get, arr, idx))) }
| LBRACE a=expr RBRACE PERCENT l=NAME VARIABLE
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($4)))
                               , CNExpr_at_env (a, l))) }
| LBRACE members=record_def RBRACE
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos,$endpos) NoCursor)
                               , CNExpr_record members)) }
| LBRACE base_value__updates=nonempty_member_updates RBRACE
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_memberupdates (fst base_value__updates, snd base_value__updates))) }
| base_value=prim_expr LBRACK updates=separated_nonempty_list(COMMA, index_update) RBRACK
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_arrayindexupdates (base_value, updates))) }



unary_expr:
| e= prim_expr
    { e }
| STAR arg = unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_deref arg)) }
| SIZEOF LT ty= ctype GT
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_sizeof ty)) }
| OFFSETOF LPAREN tag = cn_variable COMMA member= cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_offsetof (tag, member))) }
| LBRACE e= expr RBRACE CN_UNCHANGED
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_unchanged e)) }
| MINUS e= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_negate e )) }
| BANG e= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_not e )) }
| DEFAULT LT bt= base_type GT
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                               , CNExpr_default bt )) }
| AMPERSAND LPAREN e= prim_expr MINUS_GT member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_membershift (e, None, member) )) }
| AMPERSAND name=cn_variable
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_addr name)) }
| LPAREN ty= base_type_explicit RPAREN expr= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               , CNExpr_cast (ty, expr))) }


mul_expr:
(* TODO *)
| e= unary_expr
     { e }
| e1= mul_expr STAR e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_mul, e1, e2))) }
| e1= mul_expr SLASH e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_div, e1, e2))) }

add_expr:
| e= mul_expr
     { e }
| e1= add_expr PLUS e2= mul_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_add, e1, e2))) }
| e1= add_expr MINUS e2= mul_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_sub, e1, e2))) }

rel_expr:
| e= add_expr
     { e }
| e1= rel_expr EQ_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_equal, e1, e2))) }
| e1= rel_expr BANG_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_inequal, e1, e2))) }
| e1= rel_expr LT e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_lt, e1, e2))) }
| e1= rel_expr GT e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_gt, e1, e2))) }
| e1= rel_expr LT_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_le, e1, e2))) }
| e1= rel_expr GT_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_ge, e1, e2))) }

bool_bin_expr:
| e= rel_expr
    { e }
| e1= bool_bin_expr AMPERSAND_AMPERSAND e2= rel_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_and, e1, e2))) }
| e1= bool_bin_expr PIPE_PIPE e2= rel_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_or, e1, e2))) }

list_expr:
| e= bool_bin_expr
    { e }
| es= delimited(LBRACK, separated_nonempty_list(COMMA, rel_expr), RBRACK)
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                               , CNExpr_list es)) }
(*
 | LBRACK COLON bty= base_type RBRACK
 | e1= rel_expr COLON_COLON e2= list_expr
  // | Head of 'bt term
  // | Tail of 'bt term
  // | NthList of int * 'bt term
;
*)

int_range:
| l= CONSTANT COMMA r= CONSTANT
    {
      match (l, r) with
        | (Cabs.CabsInteger_const (l_str, None), Cabs.CabsInteger_const (r_str, None)) ->
            (Z.of_string l_str, Z.of_string r_str)
        | _ ->
            raise (C_lexer.Error (Cparser_unexpected_token "TODO cn integer const"))
    }

member_def:
| member=cn_variable COLON e=expr
     { (member, e) }

member_updates:
| update=member_def COMMA base_value__updates=member_updates
     { (fst base_value__updates, update::snd base_value__updates) }
| DOT DOT base_value=expr
     { (base_value,[]) }

nonempty_member_updates:
| update=member_def COMMA base_value__updates=member_updates
     { (fst base_value__updates, update::snd base_value__updates) }


index_update:
| i=prim_expr COLON e=expr
     { (i, e) }

match_cases:  (* NOTE: the list is in reverse *)
| m= match_case
    { [ m ] }
| ms= match_cases m= match_case
    { m :: ms }

pattern_member_def:
| member=cn_variable COLON p=pattern
     { (member, p) }

pattern_cons_args:
| xs= delimited(LBRACE, separated_list(COMMA, pattern_member_def), RBRACE)
    { xs }

pattern: (* very limited subset of Rust options *)
| CN_WILD
    { Cerb_frontend.Cn.(CNPat (Cerb_location.point $startpos, CNPat_wild)) }
| ident= cn_variable
    { Cerb_frontend.Cn.(CNPat (Cerb_location.point $startpos, CNPat_sym ident)) }
(* TODO require `ident` starts with an upper case *)
| ident= cn_variable args= pattern_cons_args
    { Cerb_frontend.Cn.(CNPat ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos(args)))
                               , CNPat_constructor (ident, args))) }


match_case:
| lhs= pattern EQ GT rhs= delimited(LBRACE, expr, RBRACE)
    { (lhs, rhs) }

match_target:
| ident= cn_variable
    { Cerb_frontend.Cn.(CNExpr (Cerb_location.point $startpos, CNExpr_var ident)) }
| e= delimited(LPAREN, expr, RPAREN)
    { e }


expr_without_let:
| e= list_expr
    { e }
| e1= list_expr QUESTION e2= list_expr COLON e3= list_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_ite (e1, e2, e3))) }
| IF e1= delimited(LPAREN, expr, RPAREN) e2= delimited(LBRACE, expr, RBRACE) ELSE e3= delimited(LBRACE,expr,RBRACE)
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                               , CNExpr_ite (e1, e2, e3))) }
| CN_EACH LPAREN bTy= base_type str= cn_variable COLON r=int_range SEMICOLON e1= expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) NoCursor)
                               ,
                               CNExpr_each (str, bTy, r, e1))) }
| CN_MATCH e= match_target LBRACE ms= match_cases RBRACE
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1)))
                               ,
                               CNExpr_match (e, List.rev ms))) }

expr:
| e=expr_without_let
    { e }
| CN_LET str= cn_variable EQ e1= expr SEMICOLON e2= expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.region ($startpos(e1), $endpos(e1)) NoCursor,
                                 CNExpr_let (str, e1, e2))) }
;



(* CN predicate definitions **************************************************)

(* base types, not including user-names (which conflict more in some places) *)
base_type_explicit:
| VOID
    { Cerb_frontend.Cn.CN_unit }
| CN_BOOL
    { Cerb_frontend.Cn.CN_bool }
| CN_INTEGER
    { Cerb_frontend.Cn.CN_integer }
| bit_ty=CN_BITS
    { let (sign,n) = bit_ty in 
      let sign = match sign with
       | `U -> CN_unsigned
       | `I -> CN_signed
      in
      Cerb_frontend.Cn.CN_bits (sign,n)
    }
| CN_REAL
    { Cerb_frontend.Cn.CN_real }
| CN_POINTER
    { Cerb_frontend.Cn.CN_loc }
| CN_ALLOC_ID
    { Cerb_frontend.Cn.CN_alloc_id }
| members= delimited(LBRACE, nonempty_cn_params, RBRACE)
    { Cerb_frontend.Cn.CN_record members }
| STRUCT id= cn_variable
    { Cerb_frontend.Cn.CN_struct id }
| CN_DATATYPE id= cn_variable
    { Cerb_frontend.Cn.CN_datatype id }
| CN_MAP LT bTy1= base_type COMMA bTy2= base_type GT
    { Cerb_frontend.Cn.CN_map (bTy1, bTy2) }
| CN_LIST LT bTy= base_type GT
    { Cerb_frontend.Cn.CN_list bTy }
| CN_TUPLE LT bTys= separated_list(COMMA, base_type) GT
    { Cerb_frontend.Cn.CN_tuple bTys }
| CN_SET LT bTy= base_type GT
    { Cerb_frontend.Cn.CN_set bTy }
;

base_type:
| t= base_type_explicit
    { t }
| v= cn_variable
    { Cerb_frontend.Cn.CN_user_type_name v }
;

cn_good:
| CN_GOOD ty= delimited(LT, ctype, GT)
    { ty }


cn_option_pred_clauses:
| clauses=delimited(LBRACE, clauses, RBRACE)
    { Some clauses }
|
    { None }


(* TODO check `nm` starts with upper case *)
cn_cons_case:
| nm= cn_variable args= delimited(LBRACE, cn_args, RBRACE)
    { (nm, args) }

cn_cons_cases:
| xs= separated_list (COMMA, cn_cons_case)
    { xs }

cn_attrs:
| nms= delimited (LBRACK, separated_list (COMMA, cn_variable), RBRACK)
    { nms }
|
    { [] }

cn_function:
| CN_FUNCTION
  cn_func_attrs= cn_attrs
  cn_func_return_bty=delimited(LPAREN, base_type, RPAREN) str= cn_variable
  cn_func_args= delimited(LPAREN, cn_args, RPAREN)
  cn_func_body= cn_option_func_body
    { (* TODO: check the name starts with lower case *)
      let loc = Cerb_location.point $startpos(str) in
      { cn_func_loc= loc
      ; cn_func_name= str
      ; cn_func_return_bty
      ; cn_func_attrs
      ; cn_func_args
      ; cn_func_body} }
cn_predicate:
| CN_PREDICATE
  cn_pred_attrs= cn_attrs
  cn_pred_output= cn_pred_output
  str= UNAME VARIABLE
  cn_pred_iargs= delimited(LPAREN, cn_args, RPAREN)
  cn_pred_clauses= cn_option_pred_clauses
    { (* TODO: check the name starts with upper case *)
      let loc = Cerb_location.point $startpos(str) in
      { cn_pred_loc= loc
      ; cn_pred_name= Symbol.Identifier (loc, str)
      ; cn_pred_attrs
      ; cn_pred_output
      ; cn_pred_iargs
      ; cn_pred_clauses} }
cn_lemma:
| CN_LEMMA
  str= cn_variable
  cn_lemma_args= delimited(LPAREN, cn_args, RPAREN)
  CN_REQUIRES cn_lemma_requires=nonempty_list(condition)
  CN_ENSURES cn_lemma_ensures=nonempty_list(condition)
    { (* TODO: check the name starts with lower case *)
      let loc = Cerb_location.point $startpos(str) in
      { cn_lemma_loc= loc
      ; cn_lemma_name= str
      ; cn_lemma_args
      ; cn_lemma_requires
      ; cn_lemma_ensures } }
cn_datatype:
| CN_DATATYPE nm= cn_variable
  cases= delimited(LBRACE, cn_cons_cases, RBRACE)
    {
      { cn_dt_loc= Cerb_location.point $startpos($1)
      ; cn_dt_name= nm
      ; cn_dt_cases= cases} }
cn_fun_spec:
| CN_SPEC
  str= cn_variable
  cn_spec_args= delimited(LPAREN, cn_args, RPAREN) SEMICOLON
  CN_REQUIRES cn_spec_requires=nonempty_list(condition)
  CN_ENSURES cn_spec_ensures=nonempty_list(condition)
    { let loc = Cerb_location.point $startpos(str) in
      { cn_spec_loc= loc
      ; cn_spec_name= str
      ; cn_spec_args
      ; cn_spec_requires
      ; cn_spec_ret_name = Symbol.Identifier (Cerb_location.unknown, "dummy")
      ; cn_spec_ensures } }
cn_type_synonym:
| CN_TYPE_SYNONYM
  str= cn_variable
  EQ
  ty= opt_paren(base_type)
    { let loc = Cerb_location.point $startpos(str) in
      { cn_tysyn_loc= loc
      ; cn_tysyn_name= str
      ; cn_tysyn_rhs= ty } }


(* all cases where cn_variable is used don't mind if they're shadowing
   a situation where the name has been assigned as a typedef *)
%inline cn_variable:
| str= NAME VARIABLE
    { Symbol.Identifier (Cerb_location.point $startpos(str), str) }
| str= NAME TYPE
    { Symbol.Identifier (Cerb_location.point $startpos(str), str) }

%inline base_type_cn_variable:
| bt=base_type str=cn_variable
    { (str, bt) }

cn_args:
| xs= separated_list(COMMA, base_type_cn_variable)
    { xs }
;

nonempty_cn_params:
| xs= separated_nonempty_list(COMMA, base_type_cn_variable)
    { xs }
;


opt_paren(A):
| x=A
    { x }
| x= delimited(LPAREN, A, RPAREN)
    { x }

cn_pred_output:
| bt= opt_paren(base_type)
    { let loc = Cerb_location.region $loc(bt) NoCursor in
      (loc,bt) }


record_def:
| xs= separated_nonempty_list(COMMA, member_def)
    { xs }
;



cons_args:
| xs= delimited(LBRACE, separated_list(COMMA, member_def), RBRACE)
    { xs }


clauses:
| c= clause SEMICOLON
    { Cerb_frontend.Cn.CN_clause (Cerb_location.region $loc NoCursor, c) }
| IF LPAREN e= expr RPAREN LBRACE c= clause SEMICOLON RBRACE ELSE LBRACE cs= clauses RBRACE
    { Cerb_frontend.Cn.CN_if (Cerb_location.region $loc NoCursor, e, c, cs) }
;

cn_option_func_body:
| cn_func_body=delimited(LBRACE, expr, RBRACE)
    { Some cn_func_body }
|
    { None }

(*
cn_func_body:
| CN_LET str= cn_variable EQ e= expr SEMICOLON c= cn_func_body
    { let loc = Cerb_location.point $startpos(str) in
      Cerb_frontend.Cn.CN_fb_letExpr (loc, str, e, c) }
| RETURN e= expr SEMICOLON
    { Cerb_frontend.Cn.CN_fb_return (Cerb_location.region $loc(e) NoCursor, e) }
| SWITCH e= delimited(LPAREN, expr, RPAREN) cs= nonempty_list(cn_func_body_case)
    { let loc = Cerb_location.point $startpos($1) in
      Cerb_frontend.Cn.CN_fb_cases (loc, e, cs) }
;

cn_func_body_case:
| CASE nm= cn_variable LBRACE body=cn_func_body RBRACE
    { (nm, body) }
*)

clause:
| CN_TAKE str= cn_variable EQ res= resource SEMICOLON c= clause
    { let loc = Cerb_location.point $startpos(str) in
      Cerb_frontend.Cn.CN_letResource (loc, str, res, c) }
| CN_LET str= cn_variable EQ e= expr SEMICOLON c= clause
    { let loc = Cerb_location.point $startpos(str) in
      Cerb_frontend.Cn.CN_letExpr (loc, str, e, c) }
| ASSERT e= delimited(LPAREN, assert_expr, RPAREN) SEMICOLON c= clause
    { Cerb_frontend.Cn.CN_assert (Cerb_location.region $loc NoCursor, e, c) }
| RETURN ret= expr
    { Cerb_frontend.Cn.CN_return (Cerb_location.region $loc(ret) NoCursor, ret) }
| RETURN
(*copying from prim_expr *)
    { Cerb_frontend.Cn.CN_return (Cerb_location.region $loc NoCursor,
        CNExpr (Cerb_location.region $loc NoCursor, CNExpr_const CNConst_unit)) }
;


assert_expr:
| CN_EACH LPAREN bTy= base_type str= cn_variable SEMICOLON e1= expr RPAREN
      LBRACE e2= expr RBRACE
    { Cerb_frontend.Cn.CN_assert_qexp ( str
                                      , bTy, e1, e2) }
| e= expr_without_let
    { Cerb_frontend.Cn.CN_assert_exp e }



resource:
| p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Cerb_frontend.Cn.CN_pred (Cerb_location.region $loc(p) NoCursor, p, es) }
| CN_EACH LPAREN bTy= base_type str= cn_variable SEMICOLON e1= expr RPAREN
       LBRACE p= pred LPAREN es= separated_list(COMMA, expr) RPAREN RBRACE
    { Cerb_frontend.Cn.CN_each ( str
                               , bTy
                               , e1
                               , Cerb_location.region $loc(p) NoCursor
                               , p
                               , es) }
;

pred:
| CN_OWNED ty= delimited(LT, ctype, GT)
    { Cerb_frontend.Cn.CN_owned (Some ty) }
| CN_OWNED
    { Cerb_frontend.Cn.CN_owned None }
| CN_BLOCK ty= delimited(LT, ctype, GT)
    { Cerb_frontend.Cn.CN_block ty }
| str= UNAME VARIABLE
    { Cerb_frontend.Cn.CN_named (Symbol.Identifier (Cerb_location.point $startpos(str), str)) }
;

ctype:
| ty= type_name
    { ty }
;


/* copying 'clause' and adjusting */
condition:
| CN_TAKE str= cn_variable EQ res= resource SEMICOLON
    { let loc = Cerb_location.point $startpos(str) in
      Cerb_frontend.Cn.CN_cletResource (loc, str, res) }
| CN_LET str= cn_variable EQ e= expr SEMICOLON
    { let loc = Cerb_location.point $startpos(str) in
      Cerb_frontend.Cn.CN_cletExpr (loc, str, e) }
| e= assert_expr SEMICOLON
    { Cerb_frontend.Cn.CN_cconstr (Cerb_location.region $loc NoCursor, e) }
;


function_spec_item:
| CN_TRUSTED SEMICOLON
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_trusted loc }
| CN_ACCESSES accs=nonempty_list(terminated(cn_variable,SEMICOLON))
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_accesses (loc, accs) }
| CN_REQUIRES cs=nonempty_list(condition)
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_requires (loc, cs) }
| CN_ENSURES cs=nonempty_list(condition)
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_ensures (loc, cs) }
| CN_FUNCTION nm=cn_variable SEMICOLON
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_mk_function (loc, nm) }

function_spec: 
| fs=list(function_spec_item) EOF
  { fs }


loop_spec:
| CN_INV cs=nonempty_list(condition) EOF
  { let loc = Cerb_location.region ($startpos, $endpos) NoCursor in
      Cerb_frontend.Cn.CN_inv (loc, cs) }

%inline to_be_instantiated:
|
    { Cerb_frontend.Cn.I_Everything }
| f=cn_variable COMMA
    { Cerb_frontend.Cn.I_Function f }
| ct=cn_good COMMA
    { Cerb_frontend.Cn.I_Good ct }

%inline to_be_extracted:
|
    { Cerb_frontend.Cn.E_Everything }
| p=pred COMMA
    { Cerb_frontend.Cn.E_Pred p }


cn_statement:
/* copying from 'resource' rule */
| CN_PACK p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc , CN_pack_unpack (Pack, p, es)) }
/* copying from 'resource' rule */
| CN_UNPACK p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc , CN_pack_unpack (Unpack, p, es)) }
| CN_HAVE a=assert_expr SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_have a) }
| CN_EXTRACT tbe=to_be_extracted e=expr SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_extract ([], tbe, e)) }
| CN_INSTANTIATE tbi=to_be_instantiated e=expr SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_instantiate (tbi, e)) }
| CN_SPLIT_CASE a=assert_expr SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_split_case a) }
| CN_UNFOLD id=cn_variable es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_unfold (id, es)) }
| CN_APPLY id=cn_variable es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_apply (id, es)) }
| ASSERT LPAREN e=assert_expr RPAREN SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_assert_stmt e) }
| INLINE names= separated_list(COMMA, cn_variable) SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_inline names) }
| CN_PRINT LPAREN e=expr RPAREN SEMICOLON
    { let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      CN_statement (loc, CN_print e) }

cn_statements:
| ls=nonempty_list(cn_statement) EOF
    { ls }

cn_toplevel_elem:
| pred= cn_predicate
    { EDecl_predCN pred }
| func= cn_function
    { EDecl_funcCN func }
| lmma= cn_lemma
    { EDecl_lemmaCN lmma }
| dt= cn_datatype
    { EDecl_datatypeCN dt }
| ts= cn_type_synonym
    { EDecl_type_synCN ts }
| spec= cn_fun_spec
    { EDecl_fun_specCN spec }
;

cn_toplevel:
| elems=list(cn_toplevel_elem) EOF
    { elems }


(* END CN *)
