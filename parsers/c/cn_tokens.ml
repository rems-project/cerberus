type token =
  | EOF

  (* Identifiers *)
  | UNAME of string
  | LNAME of string
  | VARIABLE
  | TYPE

  (* Keywords *)
  | CN_ACCESSES
  | CN_ALLOC_ID
  | CN_APPLY
  | CN_ARRAY_SHIFT
  | ASSERT
  | CN_BLOCK
  | CN_BOOL
  | CN_BITS of ([`U|`I] * int)
  | CN_DATATYPE
  | DEFAULT
  | CN_EACH
  | ELSE
  | CN_ENSURES
  | CN_EXTRACT
  | CN_FALSE
  | CN_FUNCTION
  | CN_GOOD
  | CN_HAVE
  | IF
  | INLINE
  | CN_INSTANTIATE
  | CN_INTEGER
  | CN_INV
  | CN_LEMMA
  | CN_LET
  | CN_LIST
  | CN_MAP
  | CN_MATCH
  | CN_MEMBER_SHIFT
  | CN_NULL
  | OFFSETOF
  | CN_OWNED
  | CN_PACK
  | CN_POINTER
  | CN_PREDICATE
  | CN_PRINT
  | CN_REAL
  | CN_REQUIRES
  | RETURN
  | CN_SET
  | SIZEOF
  | CN_SPEC
  | CN_SPLIT_CASE
  | STRUCT
  | CN_TAKE
  | CN_TRUE
  | CN_TRUSTED
  | CN_TUPLE
  | CN_TYPE_SYNONYM
  | CN_UNCHANGED
  | CN_UNFOLD
  | CN_UNPACK
  | VOID

  | CONSTANT of Cerb_frontend.Cabs.cabs_constant
  | CN_CONSTANT of (string * [`I|`U] * int)

  (* Punctuators *)
  | LBRACK
  | RBRACK
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | DOT
  | MINUS_GT
  | AMPERSAND
  | STAR
  | PLUS
  | MINUS
  | BANG
  | SLASH
  | PERCENT
  | LT
  | GT
  | LT_EQ
  | GT_EQ
  | EQ_EQ
  | BANG_EQ
  | AMPERSAND_AMPERSAND
  | PIPE_PIPE
  | QUESTION
  | COLON
  | SEMICOLON
  | EQ
  | COMMA
  (* TODO(K): add ==> *)
  | CN_WILD


let string_of_token = function
  | EOF -> "EOF"

  | UNAME s -> "UNAME(" ^ s ^ ")"
  | LNAME s -> "LNAME(" ^ s ^ ")"
  | VARIABLE -> "VARIABLE"
  | TYPE -> "TYPE"

  | CN_ACCESSES -> "CN_ACCESSES"
  | CN_ALLOC_ID -> "CN_ALLOC_ID"
  | CN_APPLY -> "CN_APPLY"
  | CN_ARRAY_SHIFT -> "CN_ARRAY_SHIFT"
  | ASSERT -> "ASSERT"
  | CN_BLOCK -> "CN_BLOCK"
  | CN_BOOL -> "CN_BOOL"
  | CN_BITS _ -> "CN_BITS"
  | CN_DATATYPE -> "CN_DATATYPE"
  | DEFAULT -> "DEFAULT"
  | CN_EACH -> "CN_EACH"
  | ELSE -> "ELSE"
  | CN_ENSURES -> "CN_ENSURES"
  | CN_EXTRACT -> "CN_EXTRACT"
  | CN_FALSE -> "CN_FALSE"
  | CN_FUNCTION -> "CN_FUNCTION"
  | CN_GOOD -> "CN_GOOD"
  | CN_HAVE -> "CN_HAVE"
  | IF -> "IF"
  | INLINE -> "INLINE"
  | CN_INSTANTIATE -> "CN_INSTANTIATE"
  | CN_INTEGER -> "CN_INTEGER"
  | CN_INV -> "CN_INV"
  | CN_LEMMA -> "CN_LEMMA"
  | CN_LET -> "CN_LET"
  | CN_LIST -> "CN_LIST"
  | CN_MAP -> "CN_MAP"
  | CN_MATCH -> "CN_MATCH"
  | CN_MEMBER_SHIFT -> "CN_MEMBER_SHIFT"
  | CN_NULL -> "CN_NULL"
  | OFFSETOF -> "OFFSETOF"
  | CN_OWNED -> "CN_OWNED"
  | CN_PACK -> "CN_PACK"
  | CN_POINTER -> "CN_POINTER"
  | CN_PREDICATE -> "CN_PREDICATE"
  | CN_PRINT -> "CN_PRINT"
  | CN_REAL -> "CN_REAL"
  | CN_REQUIRES -> "CN_REQUIRES"
  | RETURN -> "RETURN"
  | CN_SET -> "CN_SET"
  | SIZEOF -> "SIZEOF"
  | CN_SPEC -> "CN_SPEC"
  | CN_SPLIT_CASE -> "CN_SPLIT_CASE"
  | STRUCT -> "STRUCT"
  | CN_TAKE -> "CN_TAKE"
  | CN_TRUE -> "CN_TRUE"
  | CN_TRUSTED -> "CN_TRUSTED"
  | CN_TUPLE -> "CN_TUPLE"
  | CN_TYPE_SYNONYM -> "CN_TYPE_SYNONYM"
  | CN_UNCHANGED -> "CN_UNCHANGED"
  | CN_UNFOLD -> "CN_UNFOLD"
  | CN_UNPACK -> "CN_UNPACK"
  | VOID -> "VOID"

  | CONSTANT _ -> "CONSTANT"
  | CN_CONSTANT _ -> "CN_CONSTANT"

  | AMPERSAND -> "AMPERSAND"
  | AMPERSAND_AMPERSAND -> "AMPERSAND_AMPERSAND"
  | BANG -> "BANG"
  | BANG_EQ -> "BANG_EQ"
  | COLON -> "COLON"
  | COMMA -> "COMMA"
  | DOT -> "DOT"
  | EQ -> "EQ"
  | EQ_EQ -> "EQ_EQ"
  | GT -> "GT"
  | GT_EQ -> "GT_EQ"
  | LBRACE -> "LBRACE"
  | LBRACK -> "LBRACK"
  | LPAREN -> "LPAREN"
  | LT -> "LT"
  | LT_EQ -> "LT_EQ"
  | MINUS -> "MINUS"
  | MINUS_GT -> "MINUS_GT"
  | PERCENT -> "PERCENT"
  | PIPE_PIPE -> "PIPE_PIE"
  | PLUS -> "PLUS"
  | QUESTION -> "QUESTION"
  | RBRACE -> "RBRACE"
  | RBRACK -> "RBRACK"
  | RPAREN -> "RPAREN"
  | SEMICOLON -> "SEMICOLON"
  | SLASH -> "SLASH"
  | STAR -> "STAR"

  | CN_WILD -> "CN_WILD"
