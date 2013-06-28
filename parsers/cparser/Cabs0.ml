open BinPos
open String

type atom = string

type cabsloc = positive

type typeSpecifier =
| Tvoid
| Tchar
| Tshort
| Tint
| Tlong
| Tfloat
| Tdouble
| Tsigned
| Tunsigned
| T_Bool
| Tnamed of atom
| Tstruct of atom option * field_group list option * attribute list
| Tunion of atom option * field_group list option * attribute list
| Tenum of atom option * ((atom*expression option)*cabsloc) list option
   * attribute list
and storage =
| AUTO
| STATIC
| EXTERN
| REGISTER
| TYPEDEF
and cvspec =
| CV_CONST
| CV_VOLATILE
| CV_RESTRICT
and spec_elem =
| SpecCV of cvspec
| SpecAttr of attribute
| SpecStorage of storage
| SpecInline
| SpecType of typeSpecifier
and decl_type =
| JUSTBASE
| ARRAY of decl_type * cvspec list * attribute list * expression option
| PTR of cvspec list * attribute list * decl_type
| PROTO of decl_type * (parameter list*bool)
and parameter =
| PARAM of spec_elem list * atom option * decl_type * attribute list
   * cabsloc
and field_group =
| Field_group of spec_elem list * (name option*expression option) list
   * cabsloc
and name =
| Name of atom * decl_type * attribute list * cabsloc
and init_name =
| Init_name of name * init_expression
and binary_operator =
| ADD
| SUB
| MUL
| DIV
| MOD
| AND
| OR
| BAND
| BOR
| XOR
| SHL
| SHR
| EQ
| NE
| LT
| GT
| LE
| GE
| ASSIGN
| ADD_ASSIGN
| SUB_ASSIGN
| MUL_ASSIGN
| DIV_ASSIGN
| MOD_ASSIGN
| BAND_ASSIGN
| BOR_ASSIGN
| XOR_ASSIGN
| SHL_ASSIGN
| SHR_ASSIGN
| COMMA
and unary_operator =
| MINUS
| PLUS
| NOT
| BNOT
| MEMOF
| ADDROF
| PREINCR
| PREDECR
| POSINCR
| POSDECR
and expression =
| UNARY of unary_operator * expression
| BINARY of binary_operator * expression * expression
| QUESTION of expression * expression * expression
| CAST of (spec_elem list*decl_type) * init_expression
| CALL of expression * expression list
| BUILTIN_VA_ARG of expression * (spec_elem list*decl_type)
| CONSTANT of constant
| VARIABLE of atom
| EXPR_SIZEOF of expression
| TYPE_SIZEOF of (spec_elem list*decl_type)
| ALIGNOF of (spec_elem list*decl_type)
| INDEX of expression * expression
| MEMBEROF of expression * atom
| MEMBEROFPTR of expression * atom
| OFFSETOF of (spec_elem list*decl_type) * atom
and integer_suffix =
| SUFFIX_UNSIGNED
| SUFFIX_UNSIGNED_LONG
| SUFFIX_UNSIGNED_LONG_LONG
| SUFFIX_LONG
| SUFFIX_LONG_LONG
and character_prefix =
| PREFIX_L
| PREFIX_u
| PREFIX_U
and encoding_prefix =
| ENCODING_u8
| ENCODING_u
| ENCODING_U
| ENCODING_L
and constant =
| CONST_INT of atom * integer_suffix option
| CONST_FLOAT of atom
| CONST_CHAR of character_prefix option * atom
| CONST_STRING of atom
and init_expression =
| NO_INIT
| SINGLE_INIT of expression
| COMPOUND_INIT of (initwhat list*init_expression) list
and initwhat =
| INFIELD_INIT of atom
| ATINDEX_INIT of expression
and attribute =
| ATTR of atom * expression list

(** val typeSpecifier_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    (atom -> 'a1) -> (atom option -> field_group list option -> attribute
    list -> 'a1) -> (atom option -> field_group list option -> attribute list
    -> 'a1) -> (atom option -> ((atom*expression option)*cabsloc) list option
    -> attribute list -> 'a1) -> typeSpecifier -> 'a1 **)

let typeSpecifier_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Tvoid -> f
| Tchar -> f0
| Tshort -> f1
| Tint -> f2
| Tlong -> f3
| Tfloat -> f4
| Tdouble -> f5
| Tsigned -> f6
| Tunsigned -> f7
| T_Bool -> f8
| Tnamed x -> f9 x
| Tstruct (x, x0, x1) -> f10 x x0 x1
| Tunion (x, x0, x1) -> f11 x x0 x1
| Tenum (x, x0, x1) -> f12 x x0 x1

(** val typeSpecifier_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    (atom -> 'a1) -> (atom option -> field_group list option -> attribute
    list -> 'a1) -> (atom option -> field_group list option -> attribute list
    -> 'a1) -> (atom option -> ((atom*expression option)*cabsloc) list option
    -> attribute list -> 'a1) -> typeSpecifier -> 'a1 **)

let typeSpecifier_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Tvoid -> f
| Tchar -> f0
| Tshort -> f1
| Tint -> f2
| Tlong -> f3
| Tfloat -> f4
| Tdouble -> f5
| Tsigned -> f6
| Tunsigned -> f7
| T_Bool -> f8
| Tnamed x -> f9 x
| Tstruct (x, x0, x1) -> f10 x x0 x1
| Tunion (x, x0, x1) -> f11 x x0 x1
| Tenum (x, x0, x1) -> f12 x x0 x1

(** val storage_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> storage -> 'a1 **)

let storage_rect f f0 f1 f2 f3 = function
| AUTO -> f
| STATIC -> f0
| EXTERN -> f1
| REGISTER -> f2
| TYPEDEF -> f3

(** val storage_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> storage -> 'a1 **)

let storage_rec f f0 f1 f2 f3 = function
| AUTO -> f
| STATIC -> f0
| EXTERN -> f1
| REGISTER -> f2
| TYPEDEF -> f3

(** val cvspec_rect : 'a1 -> 'a1 -> 'a1 -> cvspec -> 'a1 **)

let cvspec_rect f f0 f1 = function
| CV_CONST -> f
| CV_VOLATILE -> f0
| CV_RESTRICT -> f1

(** val cvspec_rec : 'a1 -> 'a1 -> 'a1 -> cvspec -> 'a1 **)

let cvspec_rec f f0 f1 = function
| CV_CONST -> f
| CV_VOLATILE -> f0
| CV_RESTRICT -> f1

(** val spec_elem_rect :
    (cvspec -> 'a1) -> (attribute -> 'a1) -> (storage -> 'a1) -> 'a1 ->
    (typeSpecifier -> 'a1) -> spec_elem -> 'a1 **)

let spec_elem_rect f f0 f1 f2 f3 = function
| SpecCV x -> f x
| SpecAttr x -> f0 x
| SpecStorage x -> f1 x
| SpecInline -> f2
| SpecType x -> f3 x

(** val spec_elem_rec :
    (cvspec -> 'a1) -> (attribute -> 'a1) -> (storage -> 'a1) -> 'a1 ->
    (typeSpecifier -> 'a1) -> spec_elem -> 'a1 **)

let spec_elem_rec f f0 f1 f2 f3 = function
| SpecCV x -> f x
| SpecAttr x -> f0 x
| SpecStorage x -> f1 x
| SpecInline -> f2
| SpecType x -> f3 x

(** val decl_type_rect :
    'a1 -> (decl_type -> 'a1 -> cvspec list -> attribute list -> expression
    option -> 'a1) -> (cvspec list -> attribute list -> decl_type -> 'a1 ->
    'a1) -> (decl_type -> 'a1 -> (parameter list*bool) -> 'a1) -> decl_type
    -> 'a1 **)

let rec decl_type_rect f f0 f1 f2 = function
| JUSTBASE -> f
| ARRAY (d0, l, l0, o) -> f0 d0 (decl_type_rect f f0 f1 f2 d0) l l0 o
| PTR (l, l0, d0) -> f1 l l0 d0 (decl_type_rect f f0 f1 f2 d0)
| PROTO (d0, p) -> f2 d0 (decl_type_rect f f0 f1 f2 d0) p

(** val decl_type_rec :
    'a1 -> (decl_type -> 'a1 -> cvspec list -> attribute list -> expression
    option -> 'a1) -> (cvspec list -> attribute list -> decl_type -> 'a1 ->
    'a1) -> (decl_type -> 'a1 -> (parameter list*bool) -> 'a1) -> decl_type
    -> 'a1 **)

let rec decl_type_rec f f0 f1 f2 = function
| JUSTBASE -> f
| ARRAY (d0, l, l0, o) -> f0 d0 (decl_type_rec f f0 f1 f2 d0) l l0 o
| PTR (l, l0, d0) -> f1 l l0 d0 (decl_type_rec f f0 f1 f2 d0)
| PROTO (d0, p) -> f2 d0 (decl_type_rec f f0 f1 f2 d0) p

(** val parameter_rect :
    (spec_elem list -> atom option -> decl_type -> attribute list -> cabsloc
    -> 'a1) -> parameter -> 'a1 **)

let parameter_rect f = function
| PARAM (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3

(** val parameter_rec :
    (spec_elem list -> atom option -> decl_type -> attribute list -> cabsloc
    -> 'a1) -> parameter -> 'a1 **)

let parameter_rec f = function
| PARAM (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3

(** val field_group_rect :
    (spec_elem list -> (name option*expression option) list -> cabsloc ->
    'a1) -> field_group -> 'a1 **)

let field_group_rect f = function
| Field_group (x, x0, x1) -> f x x0 x1

(** val field_group_rec :
    (spec_elem list -> (name option*expression option) list -> cabsloc ->
    'a1) -> field_group -> 'a1 **)

let field_group_rec f = function
| Field_group (x, x0, x1) -> f x x0 x1

(** val name_rect :
    (atom -> decl_type -> attribute list -> cabsloc -> 'a1) -> name -> 'a1 **)

let name_rect f = function
| Name (x, x0, x1, x2) -> f x x0 x1 x2

(** val name_rec :
    (atom -> decl_type -> attribute list -> cabsloc -> 'a1) -> name -> 'a1 **)

let name_rec f = function
| Name (x, x0, x1, x2) -> f x x0 x1 x2

(** val init_name_rect :
    (name -> init_expression -> 'a1) -> init_name -> 'a1 **)

let init_name_rect f = function
| Init_name (x, x0) -> f x x0

(** val init_name_rec :
    (name -> init_expression -> 'a1) -> init_name -> 'a1 **)

let init_name_rec f = function
| Init_name (x, x0) -> f x x0

(** val binary_operator_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    binary_operator -> 'a1 **)

let binary_operator_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 = function
| ADD -> f
| SUB -> f0
| MUL -> f1
| DIV -> f2
| MOD -> f3
| AND -> f4
| OR -> f5
| BAND -> f6
| BOR -> f7
| XOR -> f8
| SHL -> f9
| SHR -> f10
| EQ -> f11
| NE -> f12
| LT -> f13
| GT -> f14
| LE -> f15
| GE -> f16
| ASSIGN -> f17
| ADD_ASSIGN -> f18
| SUB_ASSIGN -> f19
| MUL_ASSIGN -> f20
| DIV_ASSIGN -> f21
| MOD_ASSIGN -> f22
| BAND_ASSIGN -> f23
| BOR_ASSIGN -> f24
| XOR_ASSIGN -> f25
| SHL_ASSIGN -> f26
| SHR_ASSIGN -> f27
| COMMA -> f28

(** val binary_operator_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    binary_operator -> 'a1 **)

let binary_operator_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 = function
| ADD -> f
| SUB -> f0
| MUL -> f1
| DIV -> f2
| MOD -> f3
| AND -> f4
| OR -> f5
| BAND -> f6
| BOR -> f7
| XOR -> f8
| SHL -> f9
| SHR -> f10
| EQ -> f11
| NE -> f12
| LT -> f13
| GT -> f14
| LE -> f15
| GE -> f16
| ASSIGN -> f17
| ADD_ASSIGN -> f18
| SUB_ASSIGN -> f19
| MUL_ASSIGN -> f20
| DIV_ASSIGN -> f21
| MOD_ASSIGN -> f22
| BAND_ASSIGN -> f23
| BOR_ASSIGN -> f24
| XOR_ASSIGN -> f25
| SHL_ASSIGN -> f26
| SHR_ASSIGN -> f27
| COMMA -> f28

(** val unary_operator_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    unary_operator -> 'a1 **)

let unary_operator_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
| MINUS -> f
| PLUS -> f0
| NOT -> f1
| BNOT -> f2
| MEMOF -> f3
| ADDROF -> f4
| PREINCR -> f5
| PREDECR -> f6
| POSINCR -> f7
| POSDECR -> f8

(** val unary_operator_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    unary_operator -> 'a1 **)

let unary_operator_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
| MINUS -> f
| PLUS -> f0
| NOT -> f1
| BNOT -> f2
| MEMOF -> f3
| ADDROF -> f4
| PREINCR -> f5
| PREDECR -> f6
| POSINCR -> f7
| POSDECR -> f8

(** val expression_rect :
    (unary_operator -> expression -> 'a1 -> 'a1) -> (binary_operator ->
    expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression -> 'a1 ->
    expression -> 'a1 -> expression -> 'a1 -> 'a1) -> ((spec_elem
    list*decl_type) -> init_expression -> 'a1) -> (expression -> 'a1 ->
    expression list -> 'a1) -> (expression -> 'a1 -> (spec_elem
    list*decl_type) -> 'a1) -> (constant -> 'a1) -> (atom -> 'a1) ->
    (expression -> 'a1 -> 'a1) -> ((spec_elem list*decl_type) -> 'a1) ->
    ((spec_elem list*decl_type) -> 'a1) -> (expression -> 'a1 -> expression
    -> 'a1 -> 'a1) -> (expression -> 'a1 -> atom -> 'a1) -> (expression ->
    'a1 -> atom -> 'a1) -> ((spec_elem list*decl_type) -> atom -> 'a1) ->
    expression -> 'a1 **)

let rec expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
| UNARY (u, e0) ->
  f u e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
| BINARY (b, e0, e1) ->
  f0 b e0
    (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0) e1
    (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1)
| QUESTION (e0, e1, e2) ->
  f1 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    e1 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1)
    e2 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e2)
| CAST (p, i) -> f2 p i
| CALL (e0, l) ->
  f3 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    l
| BUILTIN_VA_ARG (e0, p) ->
  f4 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    p
| CONSTANT c -> f5 c
| VARIABLE a -> f6 a
| EXPR_SIZEOF e0 ->
  f7 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
| TYPE_SIZEOF p -> f8 p
| ALIGNOF p -> f9 p
| INDEX (e0, e1) ->
  f10 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    e1 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1)
| MEMBEROF (e0, a) ->
  f11 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    a
| MEMBEROFPTR (e0, a) ->
  f12 e0 (expression_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    a
| OFFSETOF (p, a) -> f13 p a

(** val expression_rec :
    (unary_operator -> expression -> 'a1 -> 'a1) -> (binary_operator ->
    expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression -> 'a1 ->
    expression -> 'a1 -> expression -> 'a1 -> 'a1) -> ((spec_elem
    list*decl_type) -> init_expression -> 'a1) -> (expression -> 'a1 ->
    expression list -> 'a1) -> (expression -> 'a1 -> (spec_elem
    list*decl_type) -> 'a1) -> (constant -> 'a1) -> (atom -> 'a1) ->
    (expression -> 'a1 -> 'a1) -> ((spec_elem list*decl_type) -> 'a1) ->
    ((spec_elem list*decl_type) -> 'a1) -> (expression -> 'a1 -> expression
    -> 'a1 -> 'a1) -> (expression -> 'a1 -> atom -> 'a1) -> (expression ->
    'a1 -> atom -> 'a1) -> ((spec_elem list*decl_type) -> atom -> 'a1) ->
    expression -> 'a1 **)

let rec expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
| UNARY (u, e0) ->
  f u e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
| BINARY (b, e0, e1) ->
  f0 b e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    e1 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1)
| QUESTION (e0, e1, e2) ->
  f1 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    e1 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1) e2
    (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e2)
| CAST (p, i) -> f2 p i
| CALL (e0, l) ->
  f3 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0) l
| BUILTIN_VA_ARG (e0, p) ->
  f4 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0) p
| CONSTANT c -> f5 c
| VARIABLE a -> f6 a
| EXPR_SIZEOF e0 ->
  f7 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
| TYPE_SIZEOF p -> f8 p
| ALIGNOF p -> f9 p
| INDEX (e0, e1) ->
  f10 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    e1 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e1)
| MEMBEROF (e0, a) ->
  f11 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    a
| MEMBEROFPTR (e0, a) ->
  f12 e0 (expression_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e0)
    a
| OFFSETOF (p, a) -> f13 p a

(** val integer_suffix_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> integer_suffix -> 'a1 **)

let integer_suffix_rect f f0 f1 f2 f3 = function
| SUFFIX_UNSIGNED -> f
| SUFFIX_UNSIGNED_LONG -> f0
| SUFFIX_UNSIGNED_LONG_LONG -> f1
| SUFFIX_LONG -> f2
| SUFFIX_LONG_LONG -> f3

(** val integer_suffix_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> integer_suffix -> 'a1 **)

let integer_suffix_rec f f0 f1 f2 f3 = function
| SUFFIX_UNSIGNED -> f
| SUFFIX_UNSIGNED_LONG -> f0
| SUFFIX_UNSIGNED_LONG_LONG -> f1
| SUFFIX_LONG -> f2
| SUFFIX_LONG_LONG -> f3

(** val character_prefix_rect :
    'a1 -> 'a1 -> 'a1 -> character_prefix -> 'a1 **)

let character_prefix_rect f f0 f1 = function
| PREFIX_L -> f
| PREFIX_u -> f0
| PREFIX_U -> f1

(** val character_prefix_rec :
    'a1 -> 'a1 -> 'a1 -> character_prefix -> 'a1 **)

let character_prefix_rec f f0 f1 = function
| PREFIX_L -> f
| PREFIX_u -> f0
| PREFIX_U -> f1

(** val encoding_prefix_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> encoding_prefix -> 'a1 **)

let encoding_prefix_rect f f0 f1 f2 = function
| ENCODING_u8 -> f
| ENCODING_u -> f0
| ENCODING_U -> f1
| ENCODING_L -> f2

(** val encoding_prefix_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> encoding_prefix -> 'a1 **)

let encoding_prefix_rec f f0 f1 f2 = function
| ENCODING_u8 -> f
| ENCODING_u -> f0
| ENCODING_U -> f1
| ENCODING_L -> f2

(** val constant_rect :
    (atom -> integer_suffix option -> 'a1) -> (atom -> 'a1) ->
    (character_prefix option -> atom -> 'a1) -> (atom -> 'a1) -> constant ->
    'a1 **)

let constant_rect f f0 f1 f2 = function
| CONST_INT (x, x0) -> f x x0
| CONST_FLOAT x -> f0 x
| CONST_CHAR (x, x0) -> f1 x x0
| CONST_STRING x -> f2 x

(** val constant_rec :
    (atom -> integer_suffix option -> 'a1) -> (atom -> 'a1) ->
    (character_prefix option -> atom -> 'a1) -> (atom -> 'a1) -> constant ->
    'a1 **)

let constant_rec f f0 f1 f2 = function
| CONST_INT (x, x0) -> f x x0
| CONST_FLOAT x -> f0 x
| CONST_CHAR (x, x0) -> f1 x x0
| CONST_STRING x -> f2 x

(** val init_expression_rect :
    'a1 -> (expression -> 'a1) -> ((initwhat list*init_expression) list ->
    'a1) -> init_expression -> 'a1 **)

let init_expression_rect f f0 f1 = function
| NO_INIT -> f
| SINGLE_INIT x -> f0 x
| COMPOUND_INIT x -> f1 x

(** val init_expression_rec :
    'a1 -> (expression -> 'a1) -> ((initwhat list*init_expression) list ->
    'a1) -> init_expression -> 'a1 **)

let init_expression_rec f f0 f1 = function
| NO_INIT -> f
| SINGLE_INIT x -> f0 x
| COMPOUND_INIT x -> f1 x

(** val initwhat_rect :
    (atom -> 'a1) -> (expression -> 'a1) -> initwhat -> 'a1 **)

let initwhat_rect f f0 = function
| INFIELD_INIT x -> f x
| ATINDEX_INIT x -> f0 x

(** val initwhat_rec :
    (atom -> 'a1) -> (expression -> 'a1) -> initwhat -> 'a1 **)

let initwhat_rec f f0 = function
| INFIELD_INIT x -> f x
| ATINDEX_INIT x -> f0 x

(** val attribute_rect :
    (atom -> expression list -> 'a1) -> attribute -> 'a1 **)

let attribute_rect f = function
| ATTR (x, x0) -> f x x0

(** val attribute_rec :
    (atom -> expression list -> 'a1) -> attribute -> 'a1 **)

let attribute_rec f = function
| ATTR (x, x0) -> f x x0

type init_name_group = spec_elem list*init_name list

type name_group = spec_elem list*name list

type definition =
| FUNDEF of spec_elem list * name * statement * cabsloc
| DECDEF of init_name_group * cabsloc
| PRAGMA of atom * cabsloc
and statement =
| NOP of cabsloc
| COMPUTATION of expression * cabsloc
| BLOCK of statement list * cabsloc
| If of expression * statement * statement option * cabsloc
| WHILE of expression * statement * cabsloc
| DOWHILE of expression * statement * cabsloc
| FOR of for_clause option * expression option * expression option
   * statement * cabsloc
| BREAK of cabsloc
| CONTINUE of cabsloc
| RETURN of expression option * cabsloc
| SWITCH of expression * statement * cabsloc
| CASE of expression * statement * cabsloc
| DEFAULT of statement * cabsloc
| LABEL of atom * statement * cabsloc
| GOTO of atom * cabsloc
| DEFINITION of definition
and for_clause =
| FC_EXP of expression
| FC_DECL of definition

(** val definition_rect :
    (spec_elem list -> name -> statement -> cabsloc -> 'a1) ->
    (init_name_group -> cabsloc -> 'a1) -> (atom -> cabsloc -> 'a1) ->
    definition -> 'a1 **)

let definition_rect f f0 f1 = function
| FUNDEF (x, x0, x1, x2) -> f x x0 x1 x2
| DECDEF (x, x0) -> f0 x x0
| PRAGMA (x, x0) -> f1 x x0

(** val definition_rec :
    (spec_elem list -> name -> statement -> cabsloc -> 'a1) ->
    (init_name_group -> cabsloc -> 'a1) -> (atom -> cabsloc -> 'a1) ->
    definition -> 'a1 **)

let definition_rec f f0 f1 = function
| FUNDEF (x, x0, x1, x2) -> f x x0 x1 x2
| DECDEF (x, x0) -> f0 x x0
| PRAGMA (x, x0) -> f1 x x0

(** val statement_rect :
    (cabsloc -> 'a1) -> (expression -> cabsloc -> 'a1) -> (statement list ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> statement option ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (for_clause option
    -> expression option -> expression option -> statement -> 'a1 -> cabsloc
    -> 'a1) -> (cabsloc -> 'a1) -> (cabsloc -> 'a1) -> (expression option ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (statement -> 'a1
    -> cabsloc -> 'a1) -> (atom -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (atom -> cabsloc -> 'a1) -> (definition -> 'a1) -> statement -> 'a1 **)

let rec statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| NOP c -> f c
| COMPUTATION (e, c) -> f0 e c
| BLOCK (l, c) -> f1 l c
| If (e, s0, o, c) ->
  f2 e s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) o
    c
| WHILE (e, s0, c) ->
  f3 e s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| DOWHILE (e, s0, c) ->
  f4 e s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| FOR (o, o0, o1, s0, c) ->
  f5 o o0 o1 s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| BREAK c -> f6 c
| CONTINUE c -> f7 c
| RETURN (o, c) -> f8 o c
| SWITCH (e, s0, c) ->
  f9 e s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| CASE (e, s0, c) ->
  f10 e s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| DEFAULT (s0, c) ->
  f11 s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| LABEL (a, s0, c) ->
  f12 a s0
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| GOTO (a, c) -> f13 a c
| DEFINITION d -> f14 d

(** val statement_rec :
    (cabsloc -> 'a1) -> (expression -> cabsloc -> 'a1) -> (statement list ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> statement option ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (for_clause option
    -> expression option -> expression option -> statement -> 'a1 -> cabsloc
    -> 'a1) -> (cabsloc -> 'a1) -> (cabsloc -> 'a1) -> (expression option ->
    cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (statement -> 'a1
    -> cabsloc -> 'a1) -> (atom -> statement -> 'a1 -> cabsloc -> 'a1) ->
    (atom -> cabsloc -> 'a1) -> (definition -> 'a1) -> statement -> 'a1 **)

let rec statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| NOP c -> f c
| COMPUTATION (e, c) -> f0 e c
| BLOCK (l, c) -> f1 l c
| If (e, s0, o, c) ->
  f2 e s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) o
    c
| WHILE (e, s0, c) ->
  f3 e s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| DOWHILE (e, s0, c) ->
  f4 e s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| FOR (o, o0, o1, s0, c) ->
  f5 o o0 o1 s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| BREAK c -> f6 c
| CONTINUE c -> f7 c
| RETURN (o, c) -> f8 o c
| SWITCH (e, s0, c) ->
  f9 e s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| CASE (e, s0, c) ->
  f10 e s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| DEFAULT (s0, c) ->
  f11 s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| LABEL (a, s0, c) ->
  f12 a s0
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0) c
| GOTO (a, c) -> f13 a c
| DEFINITION d -> f14 d

(** val for_clause_rect :
    (expression -> 'a1) -> (definition -> 'a1) -> for_clause -> 'a1 **)

let for_clause_rect f f0 = function
| FC_EXP x -> f x
| FC_DECL x -> f0 x

(** val for_clause_rec :
    (expression -> 'a1) -> (definition -> 'a1) -> for_clause -> 'a1 **)

let for_clause_rec f f0 = function
| FC_EXP x -> f x
| FC_DECL x -> f0 x

