%{

open Cerb_frontend
open Cn

(* TODO(K): work-in-progress *)
(* this is needed while this module uses a subset of Tokens.token *)
[@@@warning "-8"]

%}

%token<Cabs.cabs_constant> CONSTANT

%token ASSERT DEFAULT ELSE IF INLINE OFFSETOF RETURN SIZEOF STRUCT VOID


(* Identifiers *)
%token<string> UNAME (* Uppercase. UNAME is either a variable identifier or a type name *)
%token<string> LNAME (* Lowercase. LNAME is either a variable identifier or a type name *)
%token VARIABLE TYPE


(* Punctuators *)
%token LBRACK RBRACK LPAREN RPAREN DOT MINUS_GT AMPERSAND STAR PLUS MINUS BANG
  SLASH PERCENT LT GT LT_EQ GT_EQ EQ_EQ BANG_EQ AMPERSAND_AMPERSAND PIPE_PIPE
  QUESTION COLON EQ COMMA

%token LBRACE RBRACE SEMICOLON

%token EOF


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

%%

%inline NAME:
| u= UNAME
    { u }
| l= LNAME
    { l }


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

    
bool_and_expr:
| e= rel_expr
    { e }
| e1= bool_and_expr AMPERSAND_AMPERSAND e2= rel_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_and, e1, e2))) }
bool_or_expr:
| e = bool_and_expr
    { e }
| e1= bool_or_expr PIPE_PIPE e2= bool_and_expr
    { Cerb_frontend.Cn.(CNExpr ( Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($2)))
                               , CNExpr_binop (CN_or, e1, e2))) }

list_expr:
| e= bool_or_expr
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
      let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      { cn_func_magic_loc= Cerb_location.unknown
      ; cn_func_loc= loc
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
      let loc = Cerb_location.(region ($startpos, $endpos) NoCursor) in
      { cn_pred_magic_loc= Cerb_location.unknown
      ; cn_pred_loc= loc
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
      { cn_lemma_magic_loc= Cerb_location.unknown
      ; cn_lemma_loc= loc
      ; cn_lemma_name= str
      ; cn_lemma_args
      ; cn_lemma_requires
      ; cn_lemma_ensures } }
cn_datatype:
| CN_DATATYPE nm= cn_variable
  cases= delimited(LBRACE, cn_cons_cases, RBRACE)
    {
      { cn_dt_magic_loc= Cerb_location.unknown
      ; cn_dt_loc= Cerb_location.(region ($startpos, $endpos) NoCursor)
      ; cn_dt_name= nm
      ; cn_dt_cases= cases} }
cn_fun_spec:
| CN_SPEC
  str= cn_variable
  cn_spec_args= delimited(LPAREN, cn_args, RPAREN) SEMICOLON
  CN_REQUIRES cn_spec_requires=nonempty_list(condition)
  CN_ENSURES cn_spec_ensures=nonempty_list(condition)
    { let loc = Cerb_location.point $startpos(str) in
      { cn_spec_magic_loc= Cerb_location.unknown
      ; cn_spec_loc= loc
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
      { cn_tysyn_magic_loc= Cerb_location.unknown
      ; cn_tysyn_loc= loc
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
| NAME (* TODO(K): work-in-progress *)
    { failwith "WIP: type_name" }
(*| ty= type_name *)
(*    { ty } *)
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
