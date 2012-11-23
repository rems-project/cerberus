%{
module C = Cabs
module L = Location

type struct_union =
  | STRUCT_
  | UNION_
%}

%token <string> IDENTIFIER
%token <string> QUALIFIER
%token <string> CONST_ENUM
%token <int64 list> CONST_CHAR
%token <int64 list> CONST_WCHAR

(* Each character is its own list element, and the terminating nul is not
   included in this list. *)
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
%token ELLIPSIS
%token COMMA QUEST
%token DQUOTE

%token BREAK CONTINUE GOTO RETURN
%token SWITCH CASE DEFAULT
%token WHILE DO FOR
%token IF
%token ELSE
%token INLINE

%token TYPEOF FUNCTION__ PRETTY_FUNCTION__
%token LABEL__

%token LBRACES_3 RBRACES_3 PIPES_3


(* TODO: organize *)
%token FLOAT DOUBLE
%token EXTERN REGISTER RESTRICT
%token TYPEDEF ALIGNAS ATOMIC
%token COMPLEX GENERIC IMAGINARY NORETURN
%token STATIC_ASSERT THREAD_LOCAL

%token<Nat_num.num * Cabs.integer_suffix option> CONST_INT


%token<Cabs.encoding_prefix option * string> STRING_LITERAL

(* operator precedence *)
%right ELSE
%left  DOT ARROW

(* Non-terminals informations *)
%start start
%type <Cabs.g_defn_l list> start

%type <Cabs.stmt_l> statement
%type <Cabs.exp_l> expression
%type <Cabs.exp_l list> argument_expression_list_opt
%type <Cabs.defn_l list> declaration



(* KKK *)
%type <((string * (Cabs.c_type -> Cabs.c_type)) * Cabs.location) option * Cabs.exp_l option> struct_declarator



%%


start:
| translation_unit EOF
    {List.rev $1}
;



declaration_list_opt:
| (* empty *)
    {[]}
| l= declaration_list
    {l}
;

declaration_list:
| d= declaration
    {[d]}
(* ATTENTION We store the list in reverse.*)
| ds= declaration_list d= declaration
    {d :: ds}
;

(* TODO *)
(* 6.4.5 String literals *)
(*
string_literal:
| encoding_prefix? DQUOTE s_char_sequence? DQUOTE {(C.ENCODING_u8, ""), L.make $startpos $endpos}
*)



(* 6.5.1.1#1 Generic selection, Syntax *)
generic_association:
| ty = type_name SEMICOLON e = assignment_expression {C.TYNAME_ASSOC (ty, e), L.make $startpos $endpos}
| DEFAULT SEMICOLON e = assignment_expression        {C.DEFAULT_ASSOC e, L.make $startpos $endpos}

generic_selection:
| GENERIC LPAREN e = assignment_expression COMMA l = separated_nonempty_list(COMMA, generic_association) RPAREN
  {C.GENERIC_SELECTION (e, l), L.make $startpos $endpos}

(* 6.5.1#1 Primary expressions, Syntax *)
primary_expression:
| id = IDENTIFIER              {C.IDENTIFIER id, L.make $startpos $endpos}
| c = constant                 {C.CONSTANT c, L.make $startpos $endpos}
| l = STRING_LITERAL           {C.STRING_LITERAL l, L.make $startpos $endpos}
| LPAREN e = expression RPAREN {e}
| g = generic_selection        {g}
;

(* 6.5.2#1 Postfix operators, Syntax *)
postfix_expression:
(* see 'primary expressions' *)
| e = primary_expression     
    {e}
(* e1[e2] *)
| e1 = postfix_expression LBRACKET e2 = expression RBRACKET
    {C.SUBSCRIPT (e1, e2), L.make $startpos $endpos}
(* f(arg1, ..., argn) *)
| f = postfix_expression LPAREN args = argument_expression_list_opt RPAREN
    {C.CALL (f, args), L.make $startpos $endpos}
(* e.id *)
| e = postfix_expression DOT id = IDENTIFIER
    {C.MEMBEROF (e, id), L.make $startpos $endpos}
(* e->id *)
| e = postfix_expression ARROW id = IDENTIFIER
    {C.MEMBEROFPTR (e, id), L.make $startpos $endpos}
(* e ++ *)
| e = postfix_expression PLUS_PLUS
    {C.UNARY (C.POSTFIX_INCR, e), L.make $startpos $endpos}
(* e -- *)
| e = postfix_expression MINUS_MINUS
    {C.UNARY (C.POSTFIX_DECR, e), L.make $startpos $endpos}
    
(* TODO I am omitting compound literals for the moment. Adding them at a later stage shouldn't pose much of a challenge.
| LPAREN type_name RPAREN LBRACE initialiser_list RBRACE
    {C.COMPOUND_LITERAL ($2, C.COMPOUND_INIT $5), $1}
| LPAREN type_name RPAREN LBRACE initialiser_list COMMA RBRACE
    {C.COMPOUND_LITERAL ($2, C.COMPOUND_INIT $5), $1}
*)
;

argument_expression_list_opt:
| (* empty *)
    {[]}
| es = argument_expression_list
    {List.rev es}
;

argument_expression_list:
| e = assignment_expression
    {[e]}
(* ATTENTION Storing list in reverse. Don't forget to reverse the list. *)
| es = argument_expression_list COMMA e = assignment_expression
    {e :: es}
(* We don't need fancy error handling ;)
| error COMMA argument_expression_list {$3}
*)
;


(* 6.5.3#1 Unary operators, Syntax *)
unary_expression:
(* see 'postfix expressions' *)
| e = postfix_expression
    {e}
(* ++ e *)
| PLUS_PLUS e = unary_expression
    {C.UNARY (C.PREFIX_INCR, e), L.make $startpos $endpos}
(* -- e *)
| MINUS_MINUS e = unary_expression
    {C.UNARY (C.PREFIX_DECR, e), L.make $startpos $endpos}
(* see 'unary operators' *)
| op = unary_operator e = cast_expression
        {C.UNARY (op, e), L.make $startpos $endpos}
(* TODO Not yet supported.
| SIZEOF unary_expression
    {C.EXPR_SIZEOF (fst $2), $1}
*)
(* sizeof(ty) *)
| SIZEOF LPAREN ty = type_name RPAREN
    {C.TYPE_SIZEOF ty, L.make $startpos $endpos}
(* alignof(ty) *)
| ALIGNOF LPAREN ty = type_name RPAREN
    {C.TYPE_ALIGNOF ty, L.make $startpos $endpos}
;

unary_operator:
| AND    {C.ADDRESS}
| STAR   {C.INDIRECTION}
| PLUS   {C.PLUS}
| MINUS  {C.MINUS}
| TILDE  {C.BNOT}
| EXCLAM {C.NOT}
;


(* 6.5.4#1 Cast operators, Syntax *)
cast_expression:
(* see 'unary expressions' *)
| e = unary_expression
    {e}
(* (ty) e *)
| LPAREN ty = type_name RPAREN e = cast_expression
    {C.CAST (ty, e), L.make $startpos $endpos}
;


(* 6.5.5#1 Multiplicative operators, Syntax *)
multiplicative_expression:
(* see 'cast expressions' *)
| e = cast_expression
    {e}
(* e1 * e2 *)
| e1 = multiplicative_expression STAR e2 = cast_expression
    {C.BINARY (C.ARITHMETIC C.MUL, e1, e2), L.make $startpos $endpos}
(* e1 / e2 *)
| e1 = multiplicative_expression SLASH e2 = cast_expression
    {C.BINARY (C.ARITHMETIC C.DIV, e1, e2), L.make $startpos $endpos}
(* e1 % e2 *)
| e1 = multiplicative_expression PERCENT e2 = cast_expression
    {C.BINARY (C.ARITHMETIC C.MOD, e1, e2), L.make $startpos $endpos}
;


(* 6.5.6#1 Additive operators, Syntax *)
additive_expression:
(* see 'multiplicative expressions' *)
| e = multiplicative_expression
    {e}
(* e1 + e2 *)
| e1 = additive_expression PLUS e2 = multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.ADD, e1, e2), L.make $startpos $endpos}
(* e1 - e2 *)
| e1 = additive_expression MINUS e2 = multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.SUB, e1, e2), L.make $startpos $endpos}
;


(* 6.5.7 Bitwise shift operators, Syntax *)
shift_expression:
(* see 'additive expressions' *)
| e = additive_expression
    {e}
(* e1 << e2 *)
| e1 = shift_expression  INF_INF e2 = additive_expression
    {C.BINARY (C.ARITHMETIC C.SHL, e1, e2), L.make $startpos $endpos}
(* e1 >> e2 *)
| e1 = shift_expression  SUP_SUP e2 = additive_expression
    {C.BINARY (C.ARITHMETIC C.SHR, e1, e2), L.make $startpos $endpos}
;


(* 6.5.8#1 Relational operators, Syntax *)
relational_expression:
(* see 'shift expressions' *)
| e = shift_expression
    {e}
(* e1 < e2 *)
| e1 = relational_expression INF e2 = shift_expression
    {C.BINARY (C.LT, e1, e2), L.make $startpos $endpos}
(* e1 > e2 *)
| e1 = relational_expression SUP e2 = shift_expression
    {C.BINARY (C.GT, e1, e2), L.make $startpos $endpos}
(* e1 <= e2 *)
| e1 = relational_expression INF_EQ e2 = shift_expression
    {C.BINARY (C.LE, e1, e2), L.make $startpos $endpos}
(* e1 >= e2 *)
| e1 = relational_expression SUP_EQ e2 = shift_expression
    {C.BINARY (C.GE, e1, e2), L.make $startpos $endpos}
;


(* 6.5.9#1 Equality operators, Syntax *)
equality_expression:
(* see 'relational expressions' *)
| e = relational_expression
    {e}
(* e1 == e2 *)
| e1 = equality_expression EQ_EQ e2 = relational_expression
    {C.BINARY (C.EQ, e1, e2), L.make $startpos $endpos}
(* e1 != e2 *)
| e1 = equality_expression EXCLAM_EQ e2 = relational_expression
    {C.BINARY (C.NE, e1, e2), L.make $startpos $endpos}
;


(* 6.5.10#1 Bitwise AND operator, Syntax *)
and_expression:
(* see 'equality expressions' *)
| e = equality_expression
    {e}
(* e1 & e2 *)
| e1 = and_expression AND e2 = equality_expression
    {C.BINARY (C.ARITHMETIC C.BAND, e1, e2), L.make $startpos $endpos}
;


(* 6.5.11#1 Bitwise exclusive OR operator *)
exclusive_or_expression:
(* see 'AND expressions' *)
| e = and_expression
    {e}
(* e1 ^ e2 *)
| e1 = exclusive_or_expression CIRC e2 = and_expression
    {C.BINARY (C.ARITHMETIC C.XOR, e1, e2), L.make $startpos $endpos}
;


(* 6.5.12#1 Bitwise inclusive OR operator *)
inclusive_or_expression:
(* see 'exclusive OR expressions' *)
| e = exclusive_or_expression
    {e}
(* e1 | e2 *)
| e1 = inclusive_or_expression PIPE e2 = exclusive_or_expression
    {C.BINARY (C.ARITHMETIC C.BOR, e1, e2), L.make $startpos $endpos}
;


(* 6.5.13#1 Logical AND operator, Syntax *)
logical_and_expression:
(* see 'inclusive OR expressions' *)
| e = inclusive_or_expression
    {e}
(* e1 && e2 *)
| e1 = logical_and_expression AND_AND e2 = inclusive_or_expression
    {C.BINARY (C.AND, e1, e2), L.make $startpos $endpos}
;


(* 6.5.14#1 Logical OR operator, Syntax *)
logical_or_expression:
(* see 'logical AND expressions' *)
| e = logical_and_expression
    {e}
(* e1 || e2 *)
| e1 = logical_or_expression PIPE_PIPE e2 = logical_and_expression
    {C.BINARY (C.OR, e1, e2), L.make $startpos $endpos}
;


(* 6.5.15#1 Conditional operator, Syntax *)
conditional_expression:
(* see 'logical OR expressions' *)
| e = logical_or_expression
    {e}
(* e1 ? e2 : e3 *)
| e1 = logical_or_expression QUEST e2 = expression COLON e3 = conditional_expression
    {C.CONDITIONAL (e1, e2, e3), L.make $startpos $endpos}
;


(* 6.5.16#1 Assignment operators, Syntax *)
assignment_expression:
(* see 'conditional expressions' *)
| e = conditional_expression
    {e}
| e1 = unary_expression op = assignment_operator e2 = assignment_expression
(* see 'assignment operators' *)
    {C.ASSIGN (op, e1, e2), L.make $startpos $endpos}

assignment_operator:
| EQ         {None}
| STAR_EQ    {Some C.MUL}
| SLASH_EQ   {Some C.DIV}
| PERCENT_EQ {Some C.MOD}
| PLUS_EQ    {Some C.ADD}
| MINUS_EQ   {Some C.SUB}
| INF_INF_EQ {Some C.SHL}
| SUP_SUP_EQ {Some C.SHR}
| AND_EQ     {Some C.BAND}
| CIRC_EQ    {Some C.XOR}
| PIPE_EQ    {Some C.BOR}
;


(* 6.5.17#1 Comma operator, Syntax *)
expression:
(* see 'assignment expressions' *)
| e = assignment_expression
    {e}
(* e1, e2 *)
| e1 = expression COMMA e2 = assignment_expression
    {C.BINARY (C.COMMA, e1, e2), L.make $startpos $endpos}
;


(* 6.6 Constant expressions *)
constant_expression:
| e = conditional_expression {e}
;


(* 6.4.4#1 Constants, Syntax *)
constant:
| c = integer_constant     {c}
(* TODO: | c = floating_constant *)
(* REMARK: this would be never used in the parser, instead enum constants
           are collected as identifier in `expression' and later converted
           back to enumeration constant in Cabs_to_ail.
| c = enumeration_constant {c} *)

(* TODO: | c = character_constant *)
(* TODO Add in later.
| CONST_CHAR				{C.CONST_CHAR (fst $1), snd $1}
| CONST_WCHAR				{C.CONST_WCHAR (fst $1), snd $1}
*)
;

integer_constant:
| c = CONST_INT {C.CONST_INT c}
(* QUESTION[K]: is this η-expansion needed ?
    { let value, suffix = c in
      C.CONST_INT (value, suffix)
    }
*)
;

(* 6.4.4.3#1 Enumeration constants, Syntax *)
(* NOT USED: see REMARK in `constant' *)
enumeration_constant:
| x = CONST_ENUM {x}
;

(* 6.7 Declarations ********************************************************* *)

(* 6.7#1 Declarations, Syntax *)
declaration:
(* | declaration_specifiers init_declarator_list_opt SEMICOLON *)
| s = declaration_specifiers l = loption(init_declarator_list) SEMICOLON (* TODO: check *)
    { let store, specs, quals = s in
      let make_def (((name, mk_type), li, exp), lo) =
        (((name, mk_type (C.BASE (quals, specs)), store), li), exp), lo in
      
      match l with
        | [] -> [] (* failwith "TODO: need to extract struct tag" *)
                
        | l  -> List.map make_def (List.rev l)}
(* TODO We don't support static assertions.
| static_assert_declaration
*)
;

declaration_specifiers_opt:
| (* empty *)
    {([], Multiset.emp, Pset.empty compare)}
| declaration_specifiers
    {$1}
;

declaration_specifiers:
| s= storage_class_specifier decls_opt= declaration_specifiers_opt
    { let store, specs, quals = decls_opt in (s :: store, specs, quals) }
| s= type_specifier decls_opt= declaration_specifiers_opt
    { let store, specs, quals = decls_opt in (store, Multiset.add s specs, quals) }
| q= type_qualifier decls_opt= declaration_specifiers_opt
    { let store, specs, quals = decls_opt in (store, specs, Pset.add q quals) }
(* TODO Keyword inline should only be used for function declarations. *)
| function_specifier declaration_specifiers_opt
    {$2}
(* TODO _Noreturn is not supported. *)
(* TODO We are don't support alignment yet.
| alignment_specifier declaration_specifiers_opt
*)
;

init_declarator_list_opt:
| (* empty *)
    {[]}
| init_declarator_list
    {List.rev $1}
;

init_declarator_list:
| init_declarator
    {[$1]}
(* ATTENTION We are storing the list in reverse. *)
| init_declarator_list COMMA init_declarator
    {$3 :: $1}
;

init_declarator:
| decl = declarator
    { let name, mk_type = decl in
      (name, mk_type, None), L.make $startpos $endpos
    }
| declarator EQ initialiser
    { let name, mk_type = $1 in
      (name, mk_type, Some $3), L.make $startpos $endpos
    }


(* 6.7.1#1 Storage-class specifier, Syntax *)
storage_class_specifier:
| TYPEDEF      {C.TYPEDEF}
| EXTERN       {C.EXTERN}
| STATIC       {C.STATIC}
| THREAD_LOCAL {C.THREAD_LOCAL}
| AUTO         {C.AUTO}
| REGISTER     {C.REGISTER}
;

(* 6.7.2#1 Type specifiers, Syntax *)
type_specifier:
| VOID     {C.VOID}
| CHAR     {C.CHAR}    
| SHORT    {C.SHORT}
| INT      {C.INT}
| LONG     {C.LONG}
| FLOAT    {Debug.error "PARSING: 'float' type-specifier not yet supported." (* (* LATER *) C.FLOAT *)}
| DOUBLE   {Debug.error "PARSING: 'double' type-specifier not yet supported." (* (* LATER *) C.DOUBLE *)}
| SIGNED   {C.SIGNED}
| UNSIGNED {C.UNSIGNED}
| BOOL     {C.BOOL}
| COMPLEX  {Debug.error "PARSING: '_Complex' type-specifier not yet supported." (* (* LATER *) C.COMPLEX *)}
(* TODO
| atomic_type_specifier     {failwith "type_specifier [atomic]: TODO" (* TODO *)} *)
| spec = struct_or_union_specifier {spec}
(*
| enum_specifier            {failwith "type_specifier [enum]: TODO" (* TODO *)}
| typedef_name              {failwith "type_specifier [typedef]: TODO" (* TODO *)}
*)
;

(* 6.7.2.1#1 Structure and union specifiers, Syntax *)
struct_or_union_specifier:
| x = struct_or_union id_opt = IDENTIFIER? LBRACE decls = struct_declaration_list RBRACE
    {match x with
      | STRUCT_ -> Cabs.STRUCT (id_opt, List.rev decls)
      | UNION_  -> Cabs.UNION (id_opt, List.rev decls)}
| x = struct_or_union id = IDENTIFIER
    {match x with
      | STRUCT_ -> Cabs.STRUCT (Some id, [])
      | UNION_  -> Cabs.UNION (Some id, [])}

struct_or_union:
| STRUCT {STRUCT_}
| UNION {UNION_}

struct_declaration_list:
| decl = struct_declaration
    {[decl]}
(* ATTENTION We are storing the list in reverse. *)
| decls = struct_declaration_list decl = struct_declaration
    {decl :: decls}

struct_declarator_list_opt:
| (* empty *)
    {[]}
| l = struct_declarator_list
    {List.rev l}

(* KKK *)
struct_declaration:
| ss_qs = specifier_qualifier_list decls = struct_declarator_list_opt SEMICOLON
     {let (ss, qs) = ss_qs in
      (ss, qs,
       List.map (fun (decl_opt, exp_opt) ->
         match decl_opt, exp_opt with
           | Some ((name, mk_type), _), Some e -> Cabs.BITFIELD (Some (name, mk_type), e)
           | None                     , Some e -> Cabs.BITFIELD (None, e)
           | Some ((name, mk_type), _), None   -> Cabs.STRUCT_DECL (name, mk_type)
           | None                     , None   -> failwith "[CParser.struct_declaration] OutOfHomeomorphism exception.") decls
(*
           | Some ((name, mk_type), _), Some e -> Cabs.BITFIELD (Some (name, mk_type (C.BASE (qs, ss))), e)
           | None                     , Some e -> Cabs.BITFIELD (None, e)
           | Some ((name, mk_type), _), None   -> Cabs.STRUCT_DECL (name, mk_type (C.BASE (qs, ss)))
           | None                     , None   -> failwith "[CParser.struct_declaration] OutOfHomeomorphism exception.") decls
*)
)}

(*
| static_assert_declaration
    {Debug.error "PARSING: struct-declaration of the shape 'static_assert_declaration' not yet supported."}
*)

specifier_qualifier_list_opt:
| (* empty *)
    {(Multiset.emp, Pset.empty compare)}
| l = specifier_qualifier_list
    {l}
;

specifier_qualifier_list:
| s = type_specifier x = specifier_qualifier_list_opt
    { let specs, quals = x in
      (Multiset.add s specs, quals)
    }
| q = type_qualifier l = specifier_qualifier_list_opt
    { let specs, quals = l in
      (specs, Pset.add q quals)
    }
;

struct_declarator_list:
| decl = struct_declarator
    {[decl]}
(* ATTENTION We are storing the list in reverse. *)
| decls = struct_declarator_list COMMA decl = struct_declarator
    {decl :: decls}

(* KKK: output of type: ((string, ctype -> ctype), expression opt) *)
struct_declarator:
| decl = declarator
    {(Some decl, None)}
| decl_opt = declarator? COLON exp = constant_expression
    {(decl_opt, Some exp)}


(* 6.7.2.2#1 Enumeration specifiers, Syntax *)
enum_specifier:
| ENUM IDENTIFIER? LBRACE enumerator_list RBRACE
    {Debug.error "PARSING: 'enum-specifier' not yet supported." (* TODO *)}
| ENUM IDENTIFIER? LBRACE enumerator_list COMMA RBRACE
    {Debug.error "PARSING: 'enum-specifier' not yet supported." (* TODO *)}
| ENUM IDENTIFIER
    {Debug.error "PARSING: 'enum-specifier' not yet supported." (* TODO *)}
;

enumerator_list:
| enumerator
    {Debug.error "PARSING: 'enumerator-list' not yet supported." (* TODO *)}
| enumerator_list COMMA enumerator
    {Debug.error "PARSING: 'enumerator-list' not yet supported." (* TODO *)}

enumerator:
| enumeration_constant
    {Debug.error "PARSING: 'enumerator' not yet supported." (* TODO *)}
| enumeration_constant EQ constant_expression
    {Debug.error "PARSING: 'enumerator' not yet supported." (* TODO *)}


(* 6.7.2.4#1 Atomic type specifiers, Syntax *)
atomic_type_specifier: 
| ATOMIC LPAREN type_name RPAREN
    {Debug.error "PARSING: atomic-type-specifier' not yet supported." (* TODO *)}


(* 6.7.3#1 Type qualifiers, Syntax *)
type_qualifier:
| CONST
    {C.CONST}
| RESTRICT
    {C.RESTRICT}
| VOLATILE
    {C.VOLATILE}
| ATOMIC
    {C.ATOMIC}


(* 6.7.4#1 Function specifiers, Syntax *)
function_specifier:
| INLINE
    {()}
| NORETURN
    {Debug.error "PARSING: 'function-specifier' _NoReturn not yet supported." (* TODO *)}


(* 6.7.5#1 Alignment specifier, Syntax *)
alignment_specifier:
| ALIGNAS LPAREN type_name RPAREN
    {Debug.error "PARSING: 'alignment-specifier' not yet supported." (* TODO *)}
| ALIGNAS LPAREN constant_expression RPAREN
    {Debug.error "PARSING: 'alignment-specifier' not yet supported." (* TODO *)}
;

(* 6.7.6#1 Declarators, Syntax *)
declarator:
| ptr_opt = pointer_opt decl = direct_declarator
    { let mk_type1 : C.c_type -> C.c_type = ptr_opt in
      let mk_type2 : C.c_type -> C.c_type = snd decl in
      (fst decl, fun t -> mk_type2 (mk_type1 t)), L.make $startpos $endpos
    }
;

direct_declarator:
| id = IDENTIFIER
    {id, fun t -> t}
| LPAREN declarator RPAREN
        { let (name, (mk_type : C.c_type -> C.c_type)), _ = $2 in
      name, fun t -> mk_type t
    }
| direct_declarator LBRACKET type_qualifier_list_opt assignment_expression? RBRACKET
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> mk_type (C.ARRAY ($3, t, $4))
    }
| direct_declarator LBRACKET STATIC type_qualifier_list_opt assignment_expression RBRACKET
    {Debug.error "PARSING: direct-declarator of the shape 'direct-declarator [static type-qualifier-list_opt assignment-expression]' not yet supported." (* LATER *)}
| direct_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET
    {Debug.error "PARSING: direct-declarator of the shape 'direct-declarator [type-qualifier-list static assignment-expression]' not yet supported." (* LATER *)}
| direct_declarator LBRACKET type_qualifier_list_opt STAR RBRACKET
    {Debug.error "PARSING: direct-declarator of the shape 'direct-declarator [type-qualifier-listopt *]' not yet supported." (* LATER *)}
| direct_declarator LPAREN parameter_type_list RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, $3)
    }
(* TODO Omitted case handles empty parameter lists. We need a special case. *)
| direct_declarator LPAREN RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, [])
    }
| direct_declarator LPAREN VOID RPAREN
    { let mk_type : C.c_type -> C.c_type = snd $1 in
      fst $1, fun t -> C.FUNCTION (mk_type t, [])
    }
(* TODO We do not support function declarations of the following style.
| direct_declarator LPAREN IDENTIFIER_list_opt RPAREN
*)
;

pointer:
| STAR type_qualifier_list_opt
    {fun t -> C.POINTER ($2, t)}
| STAR type_qualifier_list_opt pointer
    { let mk_type : C.c_type -> C.c_type = $3 in
      fun t -> mk_type (C.POINTER ($2, t))
    }
;

pointer_opt:
| (* empty *)
    {fun t -> t}
| pointer
    {$1}
;

type_qualifier_list_opt:
| (* empty *)
    {Pset.empty compare}
| type_qualifier_list
    {$1}
;

type_qualifier_list:
| type_qualifier
    {Pset.add $1 (Pset.empty compare)}
| type_qualifier_list type_qualifier
    {Pset.add $2 $1}
;



(* 6.7.6#1 Declarators, Syntax *)

parameter_type_list:
| parameter_list
    {List.rev $1}
(* TODO No support for functions with a variable number of actuals
| parameter_list COMMA ELLIPSES
*)
;

parameter_list:
| parameter_declaration
    {[$1]}
(* ATTENTION We are storing the list in reverse. *)
| parameter_list COMMA parameter_declaration
    {$3 :: $1}
;

parameter_declaration:
| declaration_specifiers declarator
    { let (name, (mk_type : C.c_type -> C.c_type)), l = $2 in
      let store, specs, quals = $1 in
      (name, mk_type (C.BASE (quals, specs)), store), l
    }
(* TODO No support for type-only parameters yet. Important since we need main (void).
| declaration_specifiers abstract_declarator_opt
    { let mk_type : C.c_type -> C.c_type = $2 in
      let store, quals, specs = $1 in
      (name, mk_type (C.BASE (quals, specs)), store, None)
    }
*)
;

(* 6.7.7#1 Type names, Syntax *)
type_name:
| specifier_qualifier_list abstract_declarator_opt
    { let specs, quals = $1 in
      $2 (C.BASE (quals, specs))
    }
;

abstract_declarator_opt:
| (* empy *)
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
| (* empty *)
    {fun t -> t}
| direct_abstract_declarator
    {$1}
;

direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN
    {  let mk_type : C.c_type -> C.c_type = $2 in
       fun t -> mk_type t
    }
| direct_abstract_declarator_opt LBRACKET type_qualifier_list_opt assignment_expression? RBRACKET
    { let mk_type : C.c_type -> C.c_type = $1 in
      fun t -> mk_type (C.ARRAY ($3, t, $4))
    }
(* TODO Add the other constructs including function pointers. *)
;


(* 6.7.8#1 Type definitions, Syntax *)
typedef_name:
| IDENTIFIER
    {$1}


(* 6.7.9#1 Initalization, Syntax *)
initialiser:
| assignment_expression {$1}
(*
| LBRACE initialiser_list RBRACE {}
| LBRACE initialiser_list COMMA RBRACE {}
*)
;

(*
initialiser_list:
| designation_opt initialiser
    {$2}
*)
(* ATTENTION We store the list in reverse. *)
(*
| initialiser_list COMMA designation_opt initialiser
    {$3 :: $1}
;
*)

designation_opt:
| (* empty *)
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
| DOT IDENTIFIER {}
;

(* 6.7.10 Static assertions *)
(*
static_assert_declaration:
| STATIC_ASSERT LPAREN constant_expression COMMA string_literal RPAREN SEMICOLON
    {Debug.error "PARSING: 'static_assert-declaration' not yet supported."
*)

(* 6.8 Statements *********************************************************** *)

(* 6.8#1 Statements and blocks, Syntax *)
statement:
| s = labeled_statement
| s = compound_statement
| s = expression_statement
| s = selection_statement
| s = iteration_statement
| s = jump_statement
    {s}
;

(* 6.8.1#1 Labeled statements, Syntax *)
labeled_statement:
| id = IDENTIFIER COLON s = statement
    {C.LABEL (id, s), L.make $startpos $endpos}
| CASE e = constant_expression COLON s = statement
    {C.CASE (e, s), L.make $startpos $endpos}
| DEFAULT COLON s = statement
    {C.DEFAULT s, L.make $startpos $endpos}
;

(* 6.8.2#1 Compound statement, Syntax *)
compound_statement:
| LBRACE l = loption(block_item_list) RBRACE
    {C.BLOCK (List.rev l), L.make $startpos $endpos}
(* TODO: cppmem's parallel composition (this is not C11) *)
| LBRACES_3 xs = separated_nonempty_list(PIPES_3, statement) RBRACES_3
    {C.PAR xs, L.make $startpos $endpos}
;


block_item_list:
| x = block_item                      {[x]}
(* ATTENTION We are storing the list in reverse. *)
| xs = block_item_list x = block_item {x :: xs}
;

block_item:
| d = declaration {C.DECLARATION d, L.make $startpos $endpos}
| s = statement   {s}
;

(* 6.8.3#1 Expression and null statement, Syntax *)
expression_statement:
| e = expression? SEMICOLON
    { let l = L.make $startpos $endpos in
      match e with
      | Some e -> C.EXPRESSION e, l
      | None   -> C.SKIP, l
    }
;

(* 6.8.4#1 Selection statements, Syntax *)
selection_statement:
| IF LPAREN e = expression RPAREN s = statement
    {C.IF (e, s, None), L.make $startpos $endpos} %prec ELSE
| IF LPAREN e = expression RPAREN s1 = statement ELSE s2 = statement
    {C.IF (e, s1, Some s2), L.make $startpos $endpos}
| SWITCH LPAREN e = expression RPAREN s = statement
    {C.SWITCH (e, s), L.make $startpos $endpos}
;

(* 6.8.5#1 Iteration statements, Syntax *)
iteration_statement:
(* while (e) s *)
| WHILE LPAREN e = expression RPAREN s = statement
    {C.WHILE (e, s), L.make $startpos $endpos}
(* do s while (e) *)
| DO s = statement WHILE LPAREN e = expression RPAREN
    {C.DO (e, s), L.make $startpos $endpos}
(* for (e1; e2; e3) s *)
| FOR LPAREN e1 = expression? SEMICOLON e2 = expression? SEMICOLON e3 = expression? RPAREN s = statement
    {C.FOR_EXP (e1, e2, e3, s), L.make $startpos $endpos}
(* for (d e1; e2) s *)
| FOR LPAREN d = declaration e1 = expression? SEMICOLON e2 = expression? RPAREN s = statement
    {C.FOR_DECL (d, e1, e2, s), L.make $startpos $endpos}
;

(* 6.8.6#1 Jump statements, Syntax *)
jump_statement:
| GOTO id = IDENTIFIER             {C.GOTO id, L.make $startpos $endpos}
| CONTINUE SEMICOLON               {C.CONTINUE, L.make $startpos $endpos}
| BREAK SEMICOLON                  {C.BREAK, L.make $startpos $endpos}
| RETURN e = expression? SEMICOLON {C.RETURN e, L.make $startpos $endpos}
;


(* 6.9 External definitions ************************************************* *)
(* 6.9#1 External definitions, Syntax *)
translation_unit:
| external_declaration
    {[$1]}
| translation_unit external_declaration (* ATTENTION We store the list in reverse. *)
    {$2 :: $1}
;

external_declaration:
| d = function_definition {d}
| d = declaration         {C.EXTERNAL_DECLARATION d, L.make $startpos $endpos}
;


(* 6.9.1#1 Function definitions, Syntax *)
function_definition:
(* TODO No support for old-style function definitions. *)
| declaration_specifiers declarator (*declaration_list_opt*) compound_statement
    { let store, specs, quals = $1 in
      let (name, (mk_type : C.c_type -> C.c_type)), l = $2 in
      let defn_l = (name, mk_type (C.BASE (quals, specs)), store), l in
      C.FUNCTION_DEFINITION (defn_l, $3), L.make $startpos $endpos
    }
;


%%
