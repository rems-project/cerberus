type token =
  | EOF

  (* '<' "C type-name" '>' *)
  | LT_CTYPE_GT of Cerb_frontend.Cabs.type_name

  (* Identifiers *)
  | UNAME of string
  | LNAME of string
  | VARIABLE
  | TYPE

  (* Keywords *)
  | ACCESSES
  | ALLOC_ID
  | APPLY
  | ARRAY_SHIFT
  | ASSERT
  | BLOCK
  | BOOL
  | BITS_TYPE of ([`U|`I] * int)
  | DATATYPE
  | DEFAULT
  | EACH
  | ELSE
  | ENSURES
  | EXTRACT
  | FALSE
  | FUNCTION
  | GOOD
  | HAVE
  | IF
  | INLINE
  | INSTANTIATE
  | INTEGER
  | INV
  | LEMMA
  | LET
  | LIST
  | MAP
  | MATCH
  | MEMBER_SHIFT
  | NULL
  | OFFSETOF
  | OWNED
  | PACK
  | POINTER
  | PREDICATE
  | PRINT
  | REAL
  | REQUIRES
  | RETURN
  | SET
  | SIZEOF
  | SPEC
  | SPLIT_CASE
  | STRUCT
  | TAKE
  | TRUE
  | TRUSTED
  | TUPLE
  | TYPE_SYNONYM
  | UNCHANGED
  | UNFOLD
  | UNPACK
  | VOID

  | INTEGER_CONSTANT of Cerb_frontend.Cabs.cabs_constant (* TODO(K): replace the payload with a plain Z.t s*)
  | BITS_CONSTANT of (string * [`I|`U] * int)

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
  | UNDERSCORE


let string_of_token = function
  | EOF -> "EOF"

  | LT_CTYPE_GT _ -> "LT_CTYPE_GT"

  | UNAME s -> "UNAME(" ^ s ^ ")"
  | LNAME s -> "LNAME(" ^ s ^ ")"
  | VARIABLE -> "VARIABLE"
  | TYPE -> "TYPE"

  | ACCESSES -> "ACCESSES"
  | ALLOC_ID -> "ALLOC_ID"
  | APPLY -> "APPLY"
  | ARRAY_SHIFT -> "ARRAY_SHIFT"
  | ASSERT -> "ASSERT"
  | BLOCK -> "BLOCK"
  | BOOL -> "BOOL"
  | BITS_TYPE _ -> "BITS_TYPE"
  | DATATYPE -> "DATATYPE"
  | DEFAULT -> "DEFAULT"
  | EACH -> "EACH"
  | ELSE -> "ELSE"
  | ENSURES -> "ENSURES"
  | EXTRACT -> "EXTRACT"
  | FALSE -> "FALSE"
  | FUNCTION -> "FUNCTION"
  | GOOD -> "GOOD"
  | HAVE -> "HAVE"
  | IF -> "IF"
  | INLINE -> "INLINE"
  | INSTANTIATE -> "INSTANTIATE"
  | INTEGER -> "INTEGER"
  | INV -> "INV"
  | LEMMA -> "LEMMA"
  | LET -> "LET"
  | LIST -> "LIST"
  | MAP -> "MAP"
  | MATCH -> "MATCH"
  | MEMBER_SHIFT -> "MEMBER_SHIFT"
  | NULL -> "NULL"
  | OFFSETOF -> "OFFSETOF"
  | OWNED -> "OWNED"
  | PACK -> "PACK"
  | POINTER -> "POINTER"
  | PREDICATE -> "PREDICATE"
  | PRINT -> "PRINT"
  | REAL -> "REAL"
  | REQUIRES -> "REQUIRES"
  | RETURN -> "RETURN"
  | SET -> "SET"
  | SIZEOF -> "SIZEOF"
  | SPEC -> "SPEC"
  | SPLIT_CASE -> "SPLIT_CASE"
  | STRUCT -> "STRUCT"
  | TAKE -> "TAKE"
  | TRUE -> "TRUE"
  | TRUSTED -> "TRUSTED"
  | TUPLE -> "TUPLE"
  | TYPE_SYNONYM -> "TYPE_SYNONYM"
  | UNCHANGED -> "UNCHANGED"
  | UNFOLD -> "UNFOLD"
  | UNPACK -> "UNPACK"
  | VOID -> "VOID"

  | INTEGER_CONSTANT _ -> "INTEGER_CONSTANT"
  | BITS_CONSTANT _ -> "BITS_CONSTANT"

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

  | UNDERSCORE -> "UNDERSCORE"
