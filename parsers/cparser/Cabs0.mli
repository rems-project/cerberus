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

val typeSpecifier_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (atom
  -> 'a1) -> (atom option -> field_group list option -> attribute list ->
  'a1) -> (atom option -> field_group list option -> attribute list -> 'a1)
  -> (atom option -> ((atom*expression option)*cabsloc) list option ->
  attribute list -> 'a1) -> typeSpecifier -> 'a1

val typeSpecifier_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (atom
  -> 'a1) -> (atom option -> field_group list option -> attribute list ->
  'a1) -> (atom option -> field_group list option -> attribute list -> 'a1)
  -> (atom option -> ((atom*expression option)*cabsloc) list option ->
  attribute list -> 'a1) -> typeSpecifier -> 'a1

val storage_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> storage -> 'a1

val storage_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> storage -> 'a1

val cvspec_rect : 'a1 -> 'a1 -> 'a1 -> cvspec -> 'a1

val cvspec_rec : 'a1 -> 'a1 -> 'a1 -> cvspec -> 'a1

val spec_elem_rect :
  (cvspec -> 'a1) -> (attribute -> 'a1) -> (storage -> 'a1) -> 'a1 ->
  (typeSpecifier -> 'a1) -> spec_elem -> 'a1

val spec_elem_rec :
  (cvspec -> 'a1) -> (attribute -> 'a1) -> (storage -> 'a1) -> 'a1 ->
  (typeSpecifier -> 'a1) -> spec_elem -> 'a1

val decl_type_rect :
  'a1 -> (decl_type -> 'a1 -> cvspec list -> attribute list -> expression
  option -> 'a1) -> (cvspec list -> attribute list -> decl_type -> 'a1 ->
  'a1) -> (decl_type -> 'a1 -> (parameter list*bool) -> 'a1) -> decl_type ->
  'a1

val decl_type_rec :
  'a1 -> (decl_type -> 'a1 -> cvspec list -> attribute list -> expression
  option -> 'a1) -> (cvspec list -> attribute list -> decl_type -> 'a1 ->
  'a1) -> (decl_type -> 'a1 -> (parameter list*bool) -> 'a1) -> decl_type ->
  'a1

val parameter_rect :
  (spec_elem list -> atom option -> decl_type -> attribute list -> cabsloc ->
  'a1) -> parameter -> 'a1

val parameter_rec :
  (spec_elem list -> atom option -> decl_type -> attribute list -> cabsloc ->
  'a1) -> parameter -> 'a1

val field_group_rect :
  (spec_elem list -> (name option*expression option) list -> cabsloc -> 'a1)
  -> field_group -> 'a1

val field_group_rec :
  (spec_elem list -> (name option*expression option) list -> cabsloc -> 'a1)
  -> field_group -> 'a1

val name_rect :
  (atom -> decl_type -> attribute list -> cabsloc -> 'a1) -> name -> 'a1

val name_rec :
  (atom -> decl_type -> attribute list -> cabsloc -> 'a1) -> name -> 'a1

val init_name_rect : (name -> init_expression -> 'a1) -> init_name -> 'a1

val init_name_rec : (name -> init_expression -> 'a1) -> init_name -> 'a1

val binary_operator_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  binary_operator -> 'a1

val binary_operator_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  binary_operator -> 'a1

val unary_operator_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  unary_operator -> 'a1

val unary_operator_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  unary_operator -> 'a1

val expression_rect :
  (unary_operator -> expression -> 'a1 -> 'a1) -> (binary_operator ->
  expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression -> 'a1 ->
  expression -> 'a1 -> expression -> 'a1 -> 'a1) -> ((spec_elem
  list*decl_type) -> init_expression -> 'a1) -> (expression -> 'a1 ->
  expression list -> 'a1) -> (expression -> 'a1 -> (spec_elem list*decl_type)
  -> 'a1) -> (constant -> 'a1) -> (atom -> 'a1) -> (expression -> 'a1 -> 'a1)
  -> ((spec_elem list*decl_type) -> 'a1) -> ((spec_elem list*decl_type) ->
  'a1) -> (expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression ->
  'a1 -> atom -> 'a1) -> (expression -> 'a1 -> atom -> 'a1) -> ((spec_elem
  list*decl_type) -> atom -> 'a1) -> expression -> 'a1

val expression_rec :
  (unary_operator -> expression -> 'a1 -> 'a1) -> (binary_operator ->
  expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression -> 'a1 ->
  expression -> 'a1 -> expression -> 'a1 -> 'a1) -> ((spec_elem
  list*decl_type) -> init_expression -> 'a1) -> (expression -> 'a1 ->
  expression list -> 'a1) -> (expression -> 'a1 -> (spec_elem list*decl_type)
  -> 'a1) -> (constant -> 'a1) -> (atom -> 'a1) -> (expression -> 'a1 -> 'a1)
  -> ((spec_elem list*decl_type) -> 'a1) -> ((spec_elem list*decl_type) ->
  'a1) -> (expression -> 'a1 -> expression -> 'a1 -> 'a1) -> (expression ->
  'a1 -> atom -> 'a1) -> (expression -> 'a1 -> atom -> 'a1) -> ((spec_elem
  list*decl_type) -> atom -> 'a1) -> expression -> 'a1

val integer_suffix_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> integer_suffix -> 'a1

val integer_suffix_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> integer_suffix -> 'a1

val character_prefix_rect : 'a1 -> 'a1 -> 'a1 -> character_prefix -> 'a1

val character_prefix_rec : 'a1 -> 'a1 -> 'a1 -> character_prefix -> 'a1

val encoding_prefix_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> encoding_prefix -> 'a1

val encoding_prefix_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> encoding_prefix -> 'a1

val constant_rect :
  (atom -> integer_suffix option -> 'a1) -> (atom -> 'a1) ->
  (character_prefix option -> atom -> 'a1) -> (atom -> 'a1) -> constant ->
  'a1

val constant_rec :
  (atom -> integer_suffix option -> 'a1) -> (atom -> 'a1) ->
  (character_prefix option -> atom -> 'a1) -> (atom -> 'a1) -> constant ->
  'a1

val init_expression_rect :
  'a1 -> (expression -> 'a1) -> ((initwhat list*init_expression) list -> 'a1)
  -> init_expression -> 'a1

val init_expression_rec :
  'a1 -> (expression -> 'a1) -> ((initwhat list*init_expression) list -> 'a1)
  -> init_expression -> 'a1

val initwhat_rect : (atom -> 'a1) -> (expression -> 'a1) -> initwhat -> 'a1

val initwhat_rec : (atom -> 'a1) -> (expression -> 'a1) -> initwhat -> 'a1

val attribute_rect : (atom -> expression list -> 'a1) -> attribute -> 'a1

val attribute_rec : (atom -> expression list -> 'a1) -> attribute -> 'a1

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

val definition_rect :
  (spec_elem list -> name -> statement -> cabsloc -> 'a1) -> (init_name_group
  -> cabsloc -> 'a1) -> (atom -> cabsloc -> 'a1) -> definition -> 'a1

val definition_rec :
  (spec_elem list -> name -> statement -> cabsloc -> 'a1) -> (init_name_group
  -> cabsloc -> 'a1) -> (atom -> cabsloc -> 'a1) -> definition -> 'a1

val statement_rect :
  (cabsloc -> 'a1) -> (expression -> cabsloc -> 'a1) -> (statement list ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> statement option ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
  (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (for_clause option ->
  expression option -> expression option -> statement -> 'a1 -> cabsloc ->
  'a1) -> (cabsloc -> 'a1) -> (cabsloc -> 'a1) -> (expression option ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
  (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (statement -> 'a1 ->
  cabsloc -> 'a1) -> (atom -> statement -> 'a1 -> cabsloc -> 'a1) -> (atom ->
  cabsloc -> 'a1) -> (definition -> 'a1) -> statement -> 'a1

val statement_rec :
  (cabsloc -> 'a1) -> (expression -> cabsloc -> 'a1) -> (statement list ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> statement option ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
  (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (for_clause option ->
  expression option -> expression option -> statement -> 'a1 -> cabsloc ->
  'a1) -> (cabsloc -> 'a1) -> (cabsloc -> 'a1) -> (expression option ->
  cabsloc -> 'a1) -> (expression -> statement -> 'a1 -> cabsloc -> 'a1) ->
  (expression -> statement -> 'a1 -> cabsloc -> 'a1) -> (statement -> 'a1 ->
  cabsloc -> 'a1) -> (atom -> statement -> 'a1 -> cabsloc -> 'a1) -> (atom ->
  cabsloc -> 'a1) -> (definition -> 'a1) -> statement -> 'a1

val for_clause_rect :
  (expression -> 'a1) -> (definition -> 'a1) -> for_clause -> 'a1

val for_clause_rec :
  (expression -> 'a1) -> (definition -> 'a1) -> for_clause -> 'a1

