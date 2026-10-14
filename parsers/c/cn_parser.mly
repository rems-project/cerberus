%{
open Cerb_frontend

open Cabs
open Cn

let pos x = C_lexer.LineMap.position x
let region (x,y) p = Cerb_location.region (pos x, pos y) p
let point x = Cerb_location.point (pos x)
let noCursor = Cerb_location.NoCursor
let pointCursor x = Cerb_location.PointCursor (pos x)

let opt_to_rev_list = function
  | None -> []
  | Some xs -> List.rev xs

let empty_specs =
  { storage_classes= []
  ; type_specifiers= []
  ; type_qualifiers= []
  ; function_specifiers= []
  ; alignment_specifiers= [] }

%}

(* Punctuators *)
%token LBRACK RBRACK LPAREN RPAREN LBRACE RBRACE DOT MINUS_GT AMPERSAND STAR
  PLUS MINUS TILDE BANG SLASH PERCENT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ CARET
  PIPE AMPERSAND_AMPERSAND PIPE_PIPE QUESTION COLON SEMICOLON ELLIPSIS EQ COMMA


(* C types keywords *)
%token ALIGNAS ATOMIC AUTO BOOL CHAR COMPLEX CONST DOUBLE ENUM EXTERN FLOAT INT
  LONG NORETURN REGISTER RESTRICT SHORT SIGNED STATIC THREAD_LOCAL TYPEDEF
  UNION UNSIGNED VOLATILE

(* C keywords also in CN *)
%token VOID STRUCT SIZEOF RETURN OFFSETOF INLINE IF ELSE DEFAULT ASSERT


%token<string> UNAME (* Uppercase names *)
%token<string> LNAME (* Lowercase names *)

%token<Cabs.cabs_constant> PLAIN_INTEGER_CONSTANT CONSTANT

(* CN syntax *)
(* %token<string> CN_PREDNAME *)
%token <[`U|`I] * int>BITS
%token ACCESSES TRUSTED REQUIRES ENSURES INV CN_GHOST
%token PACK UNPACK DERIVE_CONSTRAINTS CN_HAVE FOCUS INSTANTIATE SPLIT_CASE UNFOLD APPLY CN_PRINT
%token BOOLEAN INTEGER REAL POINTER ALLOC_ID MAP CN_LIST CN_TUPLE CN_SET
%token LET TAKE RW W EACH CN_FUNCTION FUNCTION LEMMA PREDICATE
%token DATATYPE TYPE_SYNONYM SPEC ARRAY_SHIFT MEMBER_SHIFT
%token UNCHANGED UNDERSCORE MATCH
%token GOOD NULL TRUE FALSE IMPLIES TO_BYTES FROM_BYTES
%token <string * [`U|`I] * int> CN_CONSTANT

%token EOF

%type<Symbol.identifier> 
  general_identifier

%type<Cabs.specifiers>
  declaration_specifiers

%type<Cabs.storage_class_specifier>
  storage_class_specifier

%type<Cabs.cabs_type_specifier>
  struct_or_union_specifier

%type<Symbol.identifier option -> (Cabs.struct_declaration list) option -> Lexing.position -> Cabs.cabs_type_specifier>
  struct_or_union

%type<Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list>
  specifier_qualifier_list

%type<Cabs.cabs_type_specifier>
  enum_specifier

// %type<Cabs.cabs_type_specifier>
//   atomic_type_specifier

%type<Cabs.cabs_type_qualifier>
  type_qualifier

%type<Cabs.function_specifier>
  function_specifier

%type<Cabs.alignment_specifier>
  alignment_specifier

%type<Cabs.pointer_declarator>
  pointer

%type<Cabs.parameter_declaration>
  parameter_declaration

%type<Cabs.type_name>
  type_name

%type<Cabs.abstract_declarator>
  abstract_declarator

%type<Cabs.direct_abstract_declarator>
  direct_abstract_declarator

%start fundef_spec
%start loop_spec
%start cn_statements
%start cn_ghost_args
%start cn_toplevel

%type<Symbol.identifier Cn.cn_base_type> base_type
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_function> cn_function
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_predicate> cn_predicate
%type<(Symbol.identifier) Cn.cn_datatype> cn_datatype
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_clauses> clauses if_clauses
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_clause> clause
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_resource> resource
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_pred> pred
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_condition> condition
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_func_spec> function_spec fundef_spec
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_loop_spec> loop_spec
%type<(Symbol.identifier, Cabs.type_name) Cn.cn_statement> cn_statement
%type<((Symbol.identifier, Cabs.type_name) Cn.cn_statement) list> cn_statements
%type<((Symbol.identifier, Cabs.type_name) Cn.cn_expr) list * Symbol.identifier list> cn_ghost_args
%type<(Symbol.identifier * Symbol.identifier Cn.cn_base_type) list> cn_args


%type<Cabs.external_declaration> cn_toplevel_elem
%type<Cabs.external_declaration list> cn_toplevel


%%

%inline NAME:
| x= UNAME
| x= LNAME
    { x }
;


(* C type-name grammar *******************************************************)

(* NOTE: This rule is declared early, so that reduce/reduce conflict is
   resolved using it. *)
typedef_name_spec:
| i= NAME
    { TSpec ((region ($startpos, $endpos) noCursor),
             TSpec_name (Identifier (point $startpos, i))) }
;

general_identifier:
 | i= NAME
    { Symbol.Identifier (region ($startpos, $endpos) noCursor, i) }
;

%inline c_constant:
| cst= PLAIN_INTEGER_CONSTANT
| cst= CONSTANT
    { cst }
;


ident_or_constant_as_c_expression:
| id= general_identifier
    { CabsExpression (region ($startpos, $endpos) noCursor, CabsEident id) }
| cst= c_constant
    { CabsExpression (region ($startpos, $endpos) noCursor, CabsEconst cst) }
;

constant_as_c_expression:
| cst= c_constant
    { CabsExpression (region ($startpos, $endpos) noCursor, CabsEconst cst) }
;


declaration_specifiers:
| sc= storage_class_specifier specs= declaration_specifiers?
    { let specs = Option.value specs ~default:empty_specs in
      { specs with storage_classes= sc::specs.storage_classes; } }
| tspec= type_specifier specs= declaration_specifiers?
    { let specs = Option.value specs ~default:empty_specs in
      { specs with type_specifiers= tspec::specs.type_specifiers; } }
| tq= type_qualifier specs= declaration_specifiers?
    { let specs = Option.value specs ~default:empty_specs in
      { specs with type_qualifiers= tq::specs.type_qualifiers; } }
| fs= function_specifier specs= declaration_specifiers?
    { let specs = Option.value specs ~default:empty_specs in
      { specs with function_specifiers= fs::specs.function_specifiers; } }
| als= alignment_specifier specs= declaration_specifiers?
    { let specs = Option.value specs ~default:empty_specs in
      { specs with alignment_specifiers= als::specs.alignment_specifiers; } }
;

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
;

type_specifier:
| VOID
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_void) }
| BOOL
    { TSpec (region ($startpos, $endpos) noCursor, TSpec_Bool) }
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
// TODO: atomic ?
// | spec= atomic_type_specifier
| spec= struct_or_union_specifier
| spec= enum_specifier
| spec= typedef_name_spec
    { spec }
// TODO: typeof ?
;

struct_or_union_specifier:
| ctor= struct_or_union i= general_identifier
    { ctor (Some i) None $endpos }
;

struct_or_union:
| STRUCT
    { fun x y epos -> TSpec (region ($startpos, epos) noCursor,
                              TSpec_struct (Annot.Attrs [], x, y)) }
| UNION
    { fun x y epos -> TSpec (region ($startpos, epos) noCursor,
                              TSpec_union (Annot.Attrs [], x, y)) }
;

specifier_qualifier_list:
| spec= type_specifier xs_opt= specifier_qualifier_list?
    { match xs_opt with
        | Some (xs, ys) -> (spec :: xs, ys)
        | None -> ([spec], []) }
| tqual= type_qualifier xs_opt= specifier_qualifier_list?
    { match xs_opt with
        | Some (xs, ys) -> (xs, tqual :: ys)
        | None -> ([], [tqual]) }
;

enum_specifier:
| ENUM i= general_identifier
    { TSpec (region ($startpos, $endpos) noCursor,
             TSpec_enum (Some i, None)) }
;

// atomic_type_specifier:
// | ATOMIC LPAREN ty= type_name RPAREN
//     { TSpec (region ($startpos, $endpos) noCursor, TSpec_Atomic ty) }
// ;

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

function_specifier:
| INLINE
    { FS_inline }
| NORETURN
    { FS_Noreturn }
;

alignment_specifier:
| ALIGNAS LPAREN ty= type_name RPAREN
    { AS_type ty }
| ALIGNAS LPAREN expr= constant_as_c_expression RPAREN
    { AS_expr expr }
;

pointer:
| STAR tquals= type_qualifier_list?
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
| param_decls= parameter_list
    { Params (List.rev param_decls, false) }
| param_decls= parameter_list COMMA ELLIPSIS
    { Params (List.rev param_decls, true) }
;

parameter_list: (* NOTE: the list is in reverse *)
| param_decl= parameter_declaration
    { [param_decl] }
| param_decls= parameter_list COMMA param_decl= parameter_declaration
    { param_decl::param_decls }
;

parameter_declaration:
// NOTE: no parameter declarations with identifiers in CN
// | specifs= declaration_specifiers
//   decltor= declarator_varname
//     { PDeclaration_decl (specifs, LF.cabs_of_declarator decltor) }
| specifs= declaration_specifiers
  abs_decltor_opt= ioption(abstract_declarator)
    { PDeclaration_abs_decl (specifs, abs_decltor_opt) }
;

type_name:
| tspecs_tquals= specifier_qualifier_list abs_declr_opt= abstract_declarator?
    { let (tspecs, tquals) = tspecs_tquals in
      Type_name (tspecs, tquals, [], abs_declr_opt) }
;

abstract_declarator:
| ptr_decltor= pointer
    { AbsDecl_pointer ptr_decltor }
| ptr_decltor_opt= ioption(pointer) dabs_decltor= direct_abstract_declarator
    { AbsDecl_direct (ptr_decltor_opt, dabs_decltor) }
;

direct_abstract_declarator:
| LPAREN abs_decltor= abstract_declarator RPAREN
    { DAbs_abs_declarator abs_decltor }
| dabs= array_abstract_declarator
| dabs= function_abstract_declarator
    { dabs }
;

array_abstract_declarator:
| dabs_decltor= ioption(direct_abstract_declarator) LBRACK
  tquals= ioption(type_qualifier_list) expr= ident_or_constant_as_c_expression? RBRACK
    { DAbs_array (dabs_decltor, ADecl (region ($startpos, $endpos) noCursor,
      Option.fold ~none:[] ~some:Fun.id tquals, false,
      Option.map (fun e -> ADeclSize_expression e) expr)) }
;

function_abstract_declarator:
| dabs_decltor= ioption(direct_abstract_declarator) LPAREN
  param_tys_opt = parameter_type_list? RPAREN
    { match param_tys_opt with
      | Some param_tys ->
        DAbs_function (dabs_decltor, param_tys)
      | None ->
        DAbs_function (dabs_decltor, Params ([], false)) }
;

(* CN grammar ****************************************************************)

prim_expr:
| NULL
    { Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_const CNConst_NULL)) }
| TRUE
    { Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_const (CNConst_bool true))) }
| FALSE
    { Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_const (CNConst_bool false))) }
| cst= PLAIN_INTEGER_CONSTANT
    {
      match cst with
        | Cabs.CabsInteger_const (str, None) ->
            let v = Z.of_string str in
            Cerb_frontend.Cn.(CNExpr ( point $startpos
                                     , CNExpr_const (CNConst_integer v) ))
        | _ ->
            (* Enforced by the CN lexer *)
            assert false
    }
| cst= CN_CONSTANT
    {
        let (str,sign,n) = cst in
        let sign = match sign with
         | `U -> Cerb_frontend.Cn.CN_unsigned
         | `I -> Cerb_frontend.Cn.CN_signed in
         let v = Z.of_string str in
         Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_const (CNConst_bits ((sign,n),v))))
    }
| ident= cn_variable
    { Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_var ident)) }
(* | ident= cn_variable DOT ident_membr= cn_variable *)
| RETURN
    { Cerb_frontend.Cn.(CNExpr (point $startpos,
        CNExpr_var (Symbol.Identifier (point $startpos($1), "return")))) }
| e= prim_expr DOT member=cn_variable
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_memberof (e, member))) }
| e= prim_expr MINUS_GT member=cn_variable
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_arrow (e, member))) }
| e= delimited(LPAREN, expr, RPAREN)
    { e }
| ARRAY_SHIFT LT ty=ctype GT LPAREN base=expr COMMA index=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_array_shift (base, Some ty, index))) }
| ARRAY_SHIFT LPAREN base=expr COMMA index=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_array_shift (base, None, index))) }
| MEMBER_SHIFT LPAREN base=expr COMMA member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_membershift (base, None, member))) }
| MEMBER_SHIFT LT tag=ctype GT LPAREN base=expr COMMA member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_membershift (base, Some tag, member))) }
| ident= cn_variable LPAREN args=separated_list(COMMA, expr) RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_call (ident, args))) }
| ct= cn_good LPAREN arg=expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_good (ct, arg))) }
| ident= cn_variable args= cons_args
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos(args))
                               , CNExpr_cons (ident, args))) }
| arr= prim_expr LBRACK idx= expr RBRACK
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_map_get, arr, idx))) }
| LBRACE a=expr RBRACE PERCENT l=NAME //VARIABLE
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($4))
                               , CNExpr_at_env (a, l))) }
| STRUCT tag=cn_variable LBRACE members=record_def RBRACE
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos,$endpos) noCursor
                               , CNExpr_struct (tag, members))) }
| LBRACE members=record_def RBRACE
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos,$endpos) noCursor
                               , CNExpr_record members)) }
| LBRACE base_value__updates=nonempty_member_updates RBRACE
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_memberupdates (fst base_value__updates, snd base_value__updates))) }
| base_value=prim_expr LBRACK updates=separated_nonempty_list(COMMA, index_update) RBRACK
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_arrayindexupdates (base_value, updates))) }
| DEFAULT LT bt= base_type GT
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) noCursor
                               , CNExpr_default bt )) }



unary_expr:
| e= prim_expr
    { e }
| STAR arg = unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_deref arg)) }
| SIZEOF LT ty= ctype GT
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_sizeof ty)) }
| OFFSETOF LPAREN tag = cn_variable COMMA member= cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_offsetof (tag, member))) }
| LBRACE e= expr RBRACE UNCHANGED
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_unchanged e)) }
| MINUS e= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_negate e )) }
| BANG e= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_not e )) }
| TILDE e= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_bnot e )) }
| AMPERSAND LPAREN e= prim_expr MINUS_GT member=cn_variable RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_membershift (e, None, member) )) }
| AMPERSAND name=cn_variable
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_addr name)) }
| LPAREN ty= base_type_explicit RPAREN expr= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               , CNExpr_cast (ty, expr))) }


mul_expr:
| e= unary_expr
     { e }
| e1= mul_expr AMPERSAND e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_band, e1, e2))) }
| e1= mul_expr CARET e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_bxor, e1, e2))) }
| e1= mul_expr STAR e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_mul, e1, e2))) }
| e1= mul_expr SLASH e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_div, e1, e2))) }
| e1= mul_expr PERCENT e2= unary_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_mod, e1, e2))) }

add_expr:
| e= mul_expr
     { e }
| e1= add_expr PLUS e2= mul_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_add, e1, e2))) }
| e1= add_expr MINUS e2= mul_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_sub, e1, e2))) }
| e1= add_expr PIPE e2= mul_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_bor, e1, e2))) }

rel_expr:
| e= add_expr
     { e }
| e1= rel_expr EQ_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_equal, e1, e2))) }
| e1= rel_expr BANG_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_inequal, e1, e2))) }
| e1= rel_expr LT e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_lt, e1, e2))) }
| e1= rel_expr GT e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_gt, e1, e2))) }
| e1= rel_expr LT_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_le, e1, e2))) }
| e1= rel_expr GT_EQ e2= add_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_ge, e1, e2))) }

    
bool_and_expr:
| e= rel_expr
    { e }
| e1= bool_and_expr AMPERSAND_AMPERSAND e2= rel_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_and, e1, e2))) }

bool_implies_expr:
| e = bool_and_expr
    { e }
| e1= bool_and_expr IMPLIES e2= bool_implies_expr (* implication arrow ==> *)
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_implies, e1, e2))) }

bool_or_expr:
| e = bool_implies_expr
    { e }
| e1= bool_or_expr PIPE_PIPE e2= bool_implies_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_binop (CN_or, e1, e2))) }

list_expr:
| e= bool_or_expr
    { e }
| es= delimited(LBRACK, separated_nonempty_list(COMMA, rel_expr), RBRACK)
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) noCursor
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
| l= PLAIN_INTEGER_CONSTANT COMMA r= PLAIN_INTEGER_CONSTANT
    {
      match (l, r) with
        | (Cabs.CabsInteger_const (l_str, None), Cabs.CabsInteger_const (r_str, None)) ->
            (Z.of_string l_str, Z.of_string r_str)
        | _ ->
            (* Enforced by the CN lexer *)
            assert false
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
| UNDERSCORE
    { Cerb_frontend.Cn.(CNPat (point $startpos, CNPat_wild)) }
| ident= cn_variable
    { Cerb_frontend.Cn.(CNPat (point $startpos, CNPat_sym ident)) }
(* TODO require `ident` starts with an upper case *)
| ident= cn_variable args= pattern_cons_args
    { Cerb_frontend.Cn.(CNPat ( region ($startpos, $endpos) (pointCursor $startpos(args))
                               , CNPat_constructor (ident, args))) }


match_case:
| lhs= pattern EQ GT rhs= delimited(LBRACE, expr, RBRACE)
    { (lhs, rhs) }

match_target:
| ident= cn_variable
    { Cerb_frontend.Cn.(CNExpr (point $startpos, CNExpr_var ident)) }
| e= delimited(LPAREN, expr, RPAREN)
    { e }


expr_without_let:
| e= list_expr
    { e }
| e1= list_expr QUESTION e2= list_expr COLON e3= list_expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($2))
                               , CNExpr_ite (e1, e2, e3))) }
| IF e1= delimited(LPAREN, expr, RPAREN) e2= delimited(LBRACE, expr, RBRACE) ELSE e3= delimited(LBRACE,expr,RBRACE)
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) noCursor
                               , CNExpr_ite (e1, e2, e3))) }
| EACH LPAREN bTy= base_type str= cn_variable COLON r=int_range SEMICOLON e1= expr RPAREN
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) noCursor
                               ,
                               CNExpr_each (str, bTy, r, e1))) }
| MATCH e= match_target LBRACE ms= match_cases RBRACE
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos, $endpos) (pointCursor $startpos($1))
                               ,
                               CNExpr_match (e, List.rev ms))) }

expr:
| e=expr_without_let
    { e }
| LET str= cn_variable EQ e1= expr SEMICOLON e2= expr
    { Cerb_frontend.Cn.(CNExpr ( region ($startpos(e1), $endpos(e1)) noCursor,
                                 CNExpr_let (str, e1, e2))) }
;



(* CN predicate definitions **************************************************)

(* base types, not including user-names (which conflict more in some places) *)
base_type_explicit:
| VOID
    { Cerb_frontend.Cn.CN_unit }
| BOOLEAN
    { Cerb_frontend.Cn.CN_bool }
| INTEGER
    { Cerb_frontend.Cn.CN_integer }
| bit_ty=BITS
    { let (sign,n) = bit_ty in 
      let sign = match sign with
       | `U -> CN_unsigned
       | `I -> CN_signed
      in
      Cerb_frontend.Cn.CN_bits (sign,n)
    }
| REAL
    { Cerb_frontend.Cn.CN_real }
| POINTER
    { Cerb_frontend.Cn.CN_loc }
| ALLOC_ID
    { Cerb_frontend.Cn.CN_alloc_id }
| members= delimited(LBRACE, nonempty_cn_params, RBRACE)
    { Cerb_frontend.Cn.CN_record members }
| STRUCT id= cn_variable
    { Cerb_frontend.Cn.CN_struct id }
| DATATYPE id= cn_variable
    { Cerb_frontend.Cn.CN_datatype id }
| MAP LT bTy1= base_type COMMA bTy2= base_type GT
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
| GOOD ty= delimited(LT, ctype, GT)
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
| FUNCTION
  cn_func_attrs= cn_attrs
  cn_func_return_bty=delimited(LPAREN, base_type, RPAREN) str= cn_variable
  cn_func_args= delimited(LPAREN, cn_args, RPAREN)
  cn_func_body= cn_option_func_body
    { (* TODO: check the name starts with lower case *)
      let loc = region ($startpos, $endpos) noCursor in
      { cn_func_magic_loc= Cerb_location.unknown
      ; cn_func_loc= loc
      ; cn_func_name= str
      ; cn_func_return_bty
      ; cn_func_attrs
      ; cn_func_args
      ; cn_func_body} }
cn_predicate:
| PREDICATE
  cn_pred_attrs= cn_attrs
  cn_pred_output= cn_pred_output
  str= UNAME //VARIABLE
  cn_pred_iargs= delimited(LPAREN, cn_args, RPAREN)
  cn_pred_clauses= cn_option_pred_clauses
    { (* TODO: check the name starts with upper case *)
      let loc = region ($startpos, $endpos) noCursor in
      { cn_pred_magic_loc= Cerb_location.unknown
      ; cn_pred_loc= loc
      ; cn_pred_name= Symbol.Identifier (loc, str)
      ; cn_pred_attrs
      ; cn_pred_output
      ; cn_pred_iargs
      ; cn_pred_clauses} }
cn_lemma:
| LEMMA
  str= cn_variable
  cn_lemma_args= delimited(LPAREN, cn_args, RPAREN)
  REQUIRES cn_lemma_requires=nonempty_list(condition)
  ENSURES cn_lemma_ensures=nonempty_list(condition)
    { (* TODO: check the name starts with lower case *)
      let loc = point $startpos(str) in
      { cn_lemma_magic_loc= Cerb_location.unknown
      ; cn_lemma_loc= loc
      ; cn_lemma_name= str
      ; cn_lemma_args
      ; cn_lemma_requires
      ; cn_lemma_ensures } }
cn_datatype:
| DATATYPE nm= cn_variable
  cases= delimited(LBRACE, cn_cons_cases, RBRACE)
    {
      { cn_dt_magic_loc= Cerb_location.unknown
      ; cn_dt_loc= region ($startpos, $endpos) noCursor
      ; cn_dt_name= nm
      ; cn_dt_cases= cases} }
cn_fun_spec:
| SPEC
  str= cn_variable
  cn_decl_args= delimited(LPAREN, cn_args, RPAREN) SEMICOLON
  cn_func_spec=function_spec
    { let loc = point $startpos(str) in
      { cn_decl_loc= loc
      ; cn_decl_name= str
      ; cn_decl_args
      ; cn_func_spec } }
cn_type_synonym:
| TYPE_SYNONYM
  str= cn_variable
  EQ
  ty= opt_paren(base_type)
    { let loc = point $startpos(str) in
      { cn_tysyn_magic_loc= Cerb_location.unknown
      ; cn_tysyn_loc= loc
      ; cn_tysyn_name= str
      ; cn_tysyn_rhs= ty } }


(* all cases where cn_variable is used don't mind if they're shadowing
   a situation where the name has been assigned as a typedef *)
%inline cn_variable:
| str= NAME // VARIABLE
    { Symbol.Identifier (point $startpos(str), str) }
// | str= NAME // TYPE
//     { Symbol.Identifier (point $startpos(str), str) }

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
    { let loc = region $loc(bt) noCursor in
      (loc,bt) }


record_def:
| xs= separated_nonempty_list(COMMA, member_def)
    { xs }
;



cons_args:
| xs= delimited(LBRACE, separated_list(COMMA, member_def), RBRACE)
    { xs }


if_clauses:
| LBRACE cs= clauses RBRACE
    { cs }
| IF LPAREN e= expr RPAREN LBRACE c= clause SEMICOLON RBRACE ELSE cs = if_clauses
    { Cerb_frontend.Cn.CN_if (region $loc noCursor, e, c, cs) }
;

clauses:
| c= clause SEMICOLON
    { Cerb_frontend.Cn.CN_clause (region $loc noCursor, c) }
| c= if_clauses
    { c }

cn_option_func_body:
| cn_func_body=delimited(LBRACE, expr, RBRACE)
    { Some cn_func_body }
|
    { None }

clause:
| TAKE str= cn_variable EQ res= resource SEMICOLON c= clause
    { let loc = point $startpos(str) in
      Cerb_frontend.Cn.CN_letResource (loc, str, res, c) }
| LET str= cn_variable EQ e= expr SEMICOLON c= clause
    { let loc = point $startpos(str) in
      Cerb_frontend.Cn.CN_letExpr (loc, str, e, c) }
| ASSERT e= delimited(LPAREN, assert_expr, RPAREN) SEMICOLON c= clause
    { Cerb_frontend.Cn.CN_assert (region $loc noCursor, e, c) }
| RETURN ret= expr
    { Cerb_frontend.Cn.CN_return (region $loc(ret) noCursor, ret) }
| RETURN
(*copying from prim_expr *)
    { Cerb_frontend.Cn.CN_return (region $loc noCursor,
        CNExpr (region $loc noCursor, CNExpr_const CNConst_unit)) }
;


assert_expr:
| EACH LPAREN bTy= base_type str= cn_variable SEMICOLON e1= expr RPAREN
      LBRACE e2= expr RBRACE
    { Cerb_frontend.Cn.CN_assert_qexp ( str
                                      , bTy, e1, e2) }
| e= expr_without_let
    { Cerb_frontend.Cn.CN_assert_exp e }



resource:
| p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Cerb_frontend.Cn.CN_pred (region $loc(p) noCursor, p, es) }
| EACH LPAREN bTy= base_type str= cn_variable SEMICOLON e1= expr RPAREN
       LBRACE p= pred LPAREN es= separated_list(COMMA, expr) RPAREN RBRACE
    { Cerb_frontend.Cn.CN_each ( str
                               , bTy
                               , e1
                               , region $loc(p) noCursor
                               , p
                               , es) }
;

pred:
| RW ty= delimited(LT, ctype, GT)
    { Cerb_frontend.Cn.CN_owned (Some ty) }
| RW
    { Cerb_frontend.Cn.CN_owned None }
| W ty= delimited(LT, ctype, GT)
    { Cerb_frontend.Cn.CN_block (Some ty) }
| W
    { Cerb_frontend.Cn.CN_block None }
| str= UNAME // VARIABLE
    { Cerb_frontend.Cn.CN_named (Symbol.Identifier (point $startpos(str), str)) }
;

ctype:
| ty= type_name
    { ty }
;


/* copying 'clause' and adjusting */
condition:
| TAKE str= cn_variable EQ res= resource SEMICOLON
    { let loc = point $startpos(str) in
      Cerb_frontend.Cn.CN_cletResource (loc, str, res) }
| LET str= cn_variable EQ e= expr SEMICOLON
    { let loc = point $startpos(str) in
      Cerb_frontend.Cn.CN_cletExpr (loc, str, e) }
| e= assert_expr SEMICOLON
    { Cerb_frontend.Cn.CN_cconstr (region $loc noCursor, e) }
;

accesses:
| ACCESSES accs=separated_nonempty_list(COMMA,cn_variable) SEMICOLON
  { accs }

accesses_or_function:
| CN_FUNCTION nm=cn_variable SEMICOLON
  { Cerb_frontend.Cn.CN_mk_function nm }
| accs=nonempty_list(accesses)
  { Cerb_frontend.Cn.CN_accesses (List.concat accs) }

ghost_binders:
| CN_GHOST g=cn_args SEMICOLON
  { g }

requires_clauses:
| REQUIRES ghost_args=option(ghost_binders)
  reqs=nonempty_list(condition)
  { Option.value ghost_args ~default:[], reqs }

ensures_clauses:
| ENSURES
  ghost_rets=option(ghost_binders)
  enss=nonempty_list(condition)
  { Option.value ghost_rets ~default:[], enss }

(* It's possible to use anonymous midrules for many of these but it results in
   auto-generated nonterminal names which make auto-generated error messages
   harder to read and understand *)
function_spec:
| trusted=option(TRUSTED SEMICOLON { () })
  acc_func=option(accesses_or_function)
  requires=option(requires_clauses)
  ensures=option(ensures_clauses)
  { let mk_region p = region p noCursor in
    let opt_loc p = Option.map (fun list -> (mk_region p, list)) in
    { cn_func_trusted = Option.map (fun () -> mk_region $loc(trusted)) trusted
    ; cn_func_acc_func = opt_loc $loc(acc_func) acc_func
    ; cn_func_requires = opt_loc $loc(requires) requires
    ; cn_func_ensures = opt_loc $loc(ensures) ensures } }

fundef_spec: 
| function_spec=function_spec EOF
  { function_spec }


loop_spec:
| INV cs=nonempty_list(condition) EOF
  { let loc = region ($startpos, $endpos) noCursor in
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

%inline cn_pack_unpack:
| PACK
    { Pack }
| UNPACK
    { Unpack }

cn_exprs_or_elipsis:
| es = separated_list(COMMA, expr)
    { Some es }
| ELLIPSIS
    { None }

pred_maybe_iargs:
| p= pred es= delimited(LPAREN, cn_exprs_or_elipsis, RPAREN)
  { (p,es) }

cn_statement:
/* copying from 'resource' rule */
| pack_unpack=cn_pack_unpack p_es=pred_maybe_iargs SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      let (p,es) = p_es in
      CN_statement (loc , CN_pack_unpack (pack_unpack, p, es)) }
| DERIVE_CONSTRAINTS preds_iargs=delimited(LPAREN, separated_list (COMMA, pred_maybe_iargs), RPAREN) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc , CN_derive_constraints preds_iargs) }
/* copying from 'resource' rule */
| TO_BYTES p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc , CN_to_from_bytes (To, p, es)) }
| FROM_BYTES p= pred es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc , CN_to_from_bytes (From, p, es)) }
| CN_HAVE a=assert_expr SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_have a) }
| FOCUS tbe=to_be_extracted e=expr SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_extract ([], tbe, e)) }
| INSTANTIATE tbi=to_be_instantiated e=expr SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_instantiate (tbi, e)) }
| SPLIT_CASE a=assert_expr SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_split_case a) }
| UNFOLD id=cn_variable es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_unfold (id, es)) }
| APPLY id=cn_variable es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_apply (id, es)) }
| ASSERT LPAREN e=assert_expr RPAREN SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_assert_stmt e) }
| INLINE names= separated_list(COMMA, cn_variable) SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_inline names) }
| CN_PRINT LPAREN e=expr RPAREN SEMICOLON
    { let loc = region ($startpos, $endpos) noCursor in
      CN_statement (loc, CN_print e) }

cn_statements:
| ls=nonempty_list(cn_statement) EOF
    { ls }

cn_ghost_args_out:
| SEMICOLON
  gso=separated_list(COMMA, cn_variable)
    { gso }

cn_ghost_args:
| gs=separated_list(COMMA, expr)
  gso=option(cn_ghost_args_out)
  EOF
    { (gs, Option.value gso ~default:[]) }

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
