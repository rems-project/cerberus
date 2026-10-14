open Cerb_frontend

type token =
  | EOF

  (* C types keywords *)
  | ALIGNAS
  | ATOMIC
  | AUTO
  | BOOL
  | CHAR
  | COMPLEX
  | CONST
  | DOUBLE
  | ENUM
  | EXTERN
  | FLOAT
  | INT
  | LONG
  | NORETURN
  | REGISTER
  | RESTRICT
  | SHORT
  | SIGNED
  | STATIC
  | THREAD_LOCAL
  | TYPEDEF
  | UNION
  | UNSIGNED
  | VOID
  | VOLATILE

  (* Keywords *)
  (* CN 'production' keywords: well-supported and suitable for general use *)
  | BITS of ([`U|`I] * int)
  | ACCESSES
  | ALLOC_ID
  | APPLY
  | ARRAY_SHIFT
  | BOOLEAN
  | DATATYPE
  | EACH
  | ENSURES
  | FALSE
  | FOCUS
  | FUNCTION
  | GOOD
  | IMPLIES
  | INSTANTIATE
  | INTEGER
  | INV
  | LEMMA
  | LET
  | MAP
  | MATCH
  | MEMBER_SHIFT
  | NULL
  | POINTER
  | PREDICATE
  | REAL
  | REQUIRES
  | RW
  | SPEC
  | SPLIT_CASE
  | TAKE
  | TRUE
  | TRUSTED
  | TYPE_SYNONYM
  | UNCHANGED
  | UNFOLD
  | W

  (* CN 'experimental' keywords - functional in some cases but not recommended for
  general use *)
  | CN_FUNCTION
  | CN_GHOST
  | CN_HAVE
  | CN_LIST
  | CN_PRINT
  | CN_SET
  | CN_TUPLE
  | FROM_BYTES
  | TO_BYTES

  (* CN 'unimplemented' keywords - non-functional, but the keyword is reserved *)
  | DERIVE_CONSTRAINTS
  | PACK
  | UNPACK

  | PLAIN_INTEGER_CONSTANT of Cabs.cabs_constant
  | CONSTANT of Cabs.cabs_constant
  | CN_CONSTANT of (string * [`I|`U] * int)

  | LNAME of string
  | UNAME of string

  | AMPERSAND
  | AMPERSAND_AMPERSAND
  | ASSERT
  | BANG
  | BANG_EQ
  | CARET
  | COLON
  | COMMA
  | DEFAULT
  | DOT
  | ELLIPSIS
  | ELSE
  | EQ
  | EQ_EQ
  | GT
  | GT_EQ
  | IF
  | INLINE
  | LBRACE
  | LBRACK
  | LPAREN
  | LT
  | LT_EQ
  | MINUS
  | MINUS_GT
  | OFFSETOF
  | PERCENT
  | PIPE
  | PIPE_PIPE
  | PLUS
  | QUESTION
  | RBRACE
  | RBRACK
  | RETURN
  | RPAREN
  | SEMICOLON
  | SIZEOF
  | SLASH
  | STAR
  | STRUCT
  | TILDE
  | UNDERSCORE


let string_of_token = function
  | EOF -> "EOF"
  | ALIGNAS -> "ALIGNAS"
  | ATOMIC -> "ATOMIC"
  | AUTO -> "AUTO"
  | BOOL -> "BOOL"
  | CHAR -> "CHAR"
  | COMPLEX -> "COMPLEX"
  | CONST -> "CONST"
  | DOUBLE -> "DOUBLE"
  | ENUM -> "ENUM"
  | EXTERN -> "EXTERN"
  | FLOAT -> "FLOAT"
  | INT -> "INT"
  | LONG -> "LONG"
  | NORETURN -> "NORETURN"
  | REGISTER -> "REGISTER"
  | RESTRICT -> "RESTRICT"
  | SHORT -> "SHORT"
  | SIGNED -> "SIGNED"
  | STATIC -> "STATIC"
  | THREAD_LOCAL -> "THREAD_LOCAL"
  | TYPEDEF -> "TYPEDEF"
  | UNION -> "UNION"
  | UNSIGNED -> "UNSIGNED"
  | VOLATILE -> "VOLATILE"
  | VOID -> "VOID"
  | BITS _ -> "BITS"
  | ACCESSES -> "ACCESSES"
  | ALLOC_ID -> "ALLOC_ID"
  | APPLY -> "APPLY"
  | ARRAY_SHIFT -> "ARRAY_SHIFT"
  | BOOLEAN -> "BOOLEAN"
  | DATATYPE -> "DATATYPE"
  | EACH -> "EACH"
  | ENSURES -> "ENSURES"
  | FALSE -> "FALSE"
  | FOCUS -> "FOCUS"
  | FUNCTION -> "FUNCTION"
  | GOOD -> "GOOD"
  | IMPLIES -> "IMPLIES"
  | INSTANTIATE -> "INSTANTIATE"
  | INTEGER -> "INTEGER"
  | INV -> "INV"
  | LEMMA -> "LEMMA"
  | LET -> "LET"
  | MAP -> "MAP"
  | MATCH -> "MATCH"
  | MEMBER_SHIFT -> "MEMBER_SHIFT"
  | NULL -> "NULL"
  | POINTER -> "POINTER"
  | PREDICATE -> "PREDICATE"
  | REAL -> "REAL"
  | REQUIRES -> "REQUIRES"
  | RW -> "RW"
  | SPEC -> "SPEC"
  | SPLIT_CASE -> "SPLIT_CASE"
  | TAKE -> "TAKE"
  | TRUE -> "TRUE"
  | TRUSTED -> "TRUSTED"
  | TYPE_SYNONYM -> "TYPE_SYNONYM"
  | UNCHANGED -> "UNCHANGED"
  | UNFOLD -> "UNFOLD"
  | W -> "W"
  | CN_FUNCTION -> "CN_FUNCTION"
  | CN_GHOST -> "CN_GHOST"
  | CN_HAVE -> "CN_HAVE"
  | CN_LIST -> "CN_LIST"
  | CN_PRINT -> "CN_PRINT"
  | CN_SET -> "CN_SET"
  | CN_TUPLE -> "CN_TUPLE"
  | FROM_BYTES -> "FROM_BYTES"
  | TO_BYTES -> "TO_BYTES"
  | DERIVE_CONSTRAINTS -> "DERIVE_CONSTRAINTS"
  | PACK -> "PACK"
  | UNPACK -> "UNPACK"
  | PLAIN_INTEGER_CONSTANT _ -> "PLAIN_INTEGER_CONSTANT"
  | CONSTANT _ -> "CONSTANT"
  | CN_CONSTANT _ -> "CN_CONSTANT"
  | LNAME _ -> "LNAME"
  | UNAME _ -> "UNAME"
  | AMPERSAND -> "AMPERSAND"
  | AMPERSAND_AMPERSAND -> "AMPERSAND_AMPERSAND"
  | ASSERT -> "ASSERT"
  | BANG -> "BANG"
  | BANG_EQ -> "BANG_EQ"
  | CARET -> "CARET"
  | COLON -> "COLON"
  | COMMA -> "COMMA"
  | DEFAULT -> "DEFAULT"
  | DOT -> "DOT"
  | ELLIPSIS -> "ELLIPSIS"
  | ELSE -> "ELSE"
  | EQ -> "EQ"
  | EQ_EQ -> "EQ_EQ"
  | GT -> "GT"
  | GT_EQ -> "GT_EQ"
  | IF -> "IF"
  | INLINE -> "INLINE"
  | LBRACE -> "LBRACE"
  | LBRACK -> "LBRACK"
  | LPAREN -> "LPAREN"
  | LT -> "LT"
  | LT_EQ -> "LT_EQ"
  | MINUS -> "MINUS"
  | MINUS_GT -> "MINUS_GT"
  | OFFSETOF -> "OFFSETOF"
  | PERCENT -> "PERCENT"
  | PIPE -> "PIPE"
  | PIPE_PIPE -> "PIPE_PIPE"
  | PLUS -> "PLUS"
  | QUESTION -> "QUESTION"
  | RBRACE -> "RBRACE"
  | RBRACK -> "RBRACK"
  | RETURN -> "RETURN"
  | RPAREN -> "RPAREN"
  | SEMICOLON -> "SEMICOLON"
  | SIZEOF -> "SIZEOF"
  | SLASH -> "SLASH"
  | STAR -> "STAR"
  | STRUCT -> "STRUCT"
  | TILDE -> "TILDE"
  | UNDERSCORE -> "UNDERSCORE"
