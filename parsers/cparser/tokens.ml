type token =
  | AUTO
  | BREAK
  | CASE
  | CHAR
  | CONST
  | CONTINUE
  | DEFAULT
  | DO
  | DOUBLE
  | ELSE
  | ENUM
  | EXTERN
  | FLOAT
  | FOR
  | GOTO
  | IF
  | INLINE
  | INT
  | LONG
  | REGISTER
  | RESTRICT
  | RETURN
  | SHORT
  | SIGNED
  | SIZEOF
  | STATIC
  | STRUCT
  | SWITCH
  | TYPEDEF
  | UNION
  | UNSIGNED
  | VOID
  | VOLATILE
  | WHILE
  | ALIGNAS
  | ALIGNOF
  | ATOMIC
  | BOOL
  | COMPLEX
  | GENERIC
  (* IMAGINARY *)
  | NORETURN
  | STATIC_ASSERT
  | THREAD_LOCAL
  | ATOMIC_LPAREN (* this is a hack to solve a grammar ambiguity (see Lexer.mll) *)
  
  | VAR_NAME     of (Cabs.cabs_identifier * Pre_parser_aux.identifier_type ref)
  | TYPEDEF_NAME of (Cabs.cabs_identifier * Pre_parser_aux.identifier_type ref)
  | UNKNOWN_NAME of (Cabs.cabs_identifier * Pre_parser_aux.identifier_type ref)
  
  | VAR_NAME2     of Cabs.cabs_identifier
  | TYPEDEF_NAME2 of Cabs.cabs_identifier
  | OTHER_NAME    of Cabs.cabs_identifier
  
  
  | CONSTANT of Cabs.cabs_constant
  
  | STRING_LITERAL of Cabs.cabs_string_literal
  
  | LBRACKET
  | RBRACKET
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | DOT
  | MINUS_GT
  | PLUS_PLUS
  | MINUS_MINUS
  | AMPERSAND
  | STAR
  | PLUS
  | MINUS
  | TILDE
  | BANG
  | SLASH
  | PERCENT
  | LT_LT
  | GT_GT
  | LT
  | GT
  | LT_EQ
  | GT_EQ
  | EQ_EQ
  | BANG_EQ
  | CARET
  | PIPE
  | AMPERSAND_AMPERSAND
  | PIPE_PIPE
  | QUESTION
  | COLON
  | SEMICOLON
  | ELLIPSIS
  | EQ
  | STAR_EQ
  | SLASH_EQ
  | PERCENT_EQ
  | PLUS_EQ
  | MINUS_EQ
  | LT_LT_EQ
  | GT_GT_EQ
  | AMPERSAND_EQ
  | CARET_EQ
  | PIPE_EQ
  | COMMA
  
  | ASSERT
  | OFFSETOF
  | LBRACES
  | PIPES
  | RBRACES
  
  | EOF




(* DEBUG *)
let string_of_identifier_type = function
  | Pre_parser_aux.VarId -> "VarId"
  | Pre_parser_aux.TypedefId -> "TypedefId"
  | Pre_parser_aux.OtherId str -> "OtherId(" ^ str ^ ")"


let string_of_token = function
  | AUTO -> "AUTO"
  | BREAK -> "BREAK"
  | CASE -> "CASE"
  | CHAR -> "CHAR"
  | CONST -> "CONST"
  | CONTINUE -> "CONTINUE"
  | DEFAULT -> "DEFAULT"
  | DO -> "DO"
  | DOUBLE -> "DOUBLE"
  | ELSE -> "ELSE"
  | ENUM -> "ENUM"
  | EXTERN -> "EXTERN"
  | FLOAT -> "FLOAT"
  | FOR -> "FOR"
  | GOTO -> "GOTO"
  | IF -> "IF"
  | INLINE -> "INLINE"
  | INT -> "INT"
  | LONG -> "LONG"
  | REGISTER -> "REGISTER"
  | RESTRICT -> "RESTRICT"
  | RETURN -> "RETURN"
  | SHORT -> "SHORT"
  | SIGNED -> "SIGNED"
  | SIZEOF -> "SIZEOF"
  | STATIC -> "STATIC"
  | STRUCT -> "STRUCT"
  | SWITCH -> "SWITCH"
  | TYPEDEF -> "TYPEDEF"
  | UNION -> "UNION"
  | UNSIGNED -> "UNSIGNED"
  | VOID -> "VOID"
  | VOLATILE -> "VOLATILE"
  | WHILE -> "WHILE"
  | ALIGNAS -> "ALIGNAS"
  | ALIGNOF -> "ALIGNOF"
  | ATOMIC -> "ATOMIC"
  | BOOL -> "BOOL"
  | COMPLEX -> "COMPLEX"
  | GENERIC -> "GENRIC"
  | NORETURN -> "NORETURN"
  | STATIC_ASSERT -> "STATIC_ASSERT"
  | THREAD_LOCAL -> "THREAD_LOCAL"
  | ATOMIC_LPAREN -> "ATOMIC_LPAREN"
  | VAR_NAME (Cabs.CabsIdentifier (_, str), id_ty) -> "VAR_NAME(" ^ str ^ ", " ^ string_of_identifier_type !id_ty ^ ")"
  | TYPEDEF_NAME (Cabs.CabsIdentifier (_, str), id_ty) -> "TYPEDEF_NAME(" ^ str ^ ", " ^ string_of_identifier_type !id_ty ^ ")"
  | UNKNOWN_NAME (Cabs.CabsIdentifier (_, str), id_ty) -> "UNKNOWN_NAME(" ^ str ^ ", " ^ string_of_identifier_type !id_ty ^ ")"
  | VAR_NAME2 (Cabs.CabsIdentifier (_, str)) -> "VAR_NAME2(" ^ str ^ ")"
  | TYPEDEF_NAME2 (Cabs.CabsIdentifier (_, str)) -> "TYPEDEF_NAME2(" ^ str ^ ")"
  | OTHER_NAME (Cabs.CabsIdentifier (_, str)) -> "OTHER_NAME(" ^ str ^ ")"
  | CONSTANT _ -> "CONSTANT"
  | STRING_LITERAL _ -> "STRING_LITERAL"
  | LBRACKET -> "LBRACKET"
  | RBRACKET -> "RBRACKET"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | DOT -> "DOT"
  | MINUS_GT -> "MINUS_GT"
  | PLUS_PLUS -> "PLUS_PLUS"
  | MINUS_MINUS -> "MINUS_MINUS"
  | AMPERSAND -> "AMPERSAND"
  | STAR -> "STAR"
  | PLUS -> "PLUS"
  | MINUS -> "MINUS"
  | TILDE -> "TILDE"
  | BANG -> "BANG"
  | SLASH -> "SLASH"
  | PERCENT -> "PERCENT"
  | LT_LT -> "LT_LT"
  | GT_GT -> "GT_GT"
  | LT -> "LT"
  | GT -> "GT"
  | LT_EQ -> "LT_EQ"
  | GT_EQ -> "GT_EQ"
  | EQ_EQ -> "EQ_EQ"
  | BANG_EQ -> "BANG_EQ"
  | CARET -> "CARET"
  | PIPE -> "PIPE"
  | AMPERSAND_AMPERSAND -> "AMPERSAND_AMPERSAND"
  | PIPE_PIPE -> "PIPE_PIE"
  | QUESTION -> "QUESTION"
  | COLON -> "COLON"
  | SEMICOLON -> "SEMICOLON"
  | ELLIPSIS -> "ELLIPSIS"
  | EQ -> "EQ"
  | STAR_EQ -> "STAR_EQ"
  | SLASH_EQ -> "SLASH_EQ"
  | PERCENT_EQ -> "PERCENT_EQ"
  | PLUS_EQ -> "PLUS_EQ"
  | MINUS_EQ -> "MINUS_EQ"
  | LT_LT_EQ -> "LT_LT_EQ"
  | GT_GT_EQ -> "GT_GT_EQ"
  | AMPERSAND_EQ -> "AMPERSAND_EQ"
  | CARET_EQ -> "CARET_EQ"
  | PIPE_EQ -> "PIPE_EQ"
  | COMMA -> "COMMA"
  | EOF -> "EOF"
