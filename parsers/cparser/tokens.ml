open Cabs0

type token = 
    (* (§6.4.1) keywords *)
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
  | IMAGINARY
  | NORETURN
  | STATIC_ASSERT
  | THREAD_LOCAL






(*


  | XOR_ASSIGN of cabsloc
  | WHILE of cabsloc
  | VOLATILE of cabsloc
  | VOID of cabsloc
  | VAR_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | UNSIGNED of cabsloc
  | UNKNOWN_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | UNION of cabsloc
  | TYPEDEF_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | TYPEDEF of cabsloc
  | TILDE of cabsloc
  | THREAD_LOCAL of cabsloc
  | SWITCH of cabsloc
  | SUB_ASSIGN of cabsloc
  | STRUCT of cabsloc
  | STRING_LITERAL of (string * cabsloc)
  | STATIC_ASSERT of cabsloc
  | STATIC of cabsloc
  | STAR of cabsloc
  | SLASH of cabsloc
  | SIZEOF of cabsloc
  | SIGNED of cabsloc
  | SHORT of cabsloc
  | SEMICOLON of cabsloc
  | RPAREN of cabsloc
  | RIGHT_ASSIGN of cabsloc
  | RIGHT of cabsloc
  | RETURN of cabsloc
  | RESTRICT of cabsloc
  | REGISTER of cabsloc
  | RBRACK of cabsloc
  | RBRACES of cabsloc
  | RBRACE of cabsloc
  | QUESTION of cabsloc
  | PTR of cabsloc
  | PLUS of cabsloc
  | PERCENT of cabsloc
  | OR_ASSIGN of cabsloc
  | OFFSETOF of cabsloc
  | NEQ of cabsloc
  | MUL_ASSIGN of cabsloc
  | MOD_ASSIGN of cabsloc
  | MINUS of cabsloc
  | LT of cabsloc
  | LPAREN of cabsloc
  | LONG of cabsloc
  | LEQ of cabsloc
  | LEFT_ASSIGN of cabsloc
  | LEFT of cabsloc
  | LBRACK of cabsloc
  | LBRACES of cabsloc
  | LBRACE of cabsloc
  | INT of cabsloc
  | INLINE of cabsloc
  | INC of cabsloc
  | IF of cabsloc
  | HAT of cabsloc
  | GT of cabsloc
  | GOTO of cabsloc
  | GEQ of cabsloc
  | FOR of cabsloc
  | FLOAT of cabsloc
  | EXTERN of cabsloc
  | EQEQ of cabsloc
  | EQ of cabsloc
  | EOF
  | ENUM of cabsloc
  | ELSE of cabsloc
  | ELLIPSIS of cabsloc
  | DOUBLE of cabsloc
  | DOT of cabsloc
  | DO of cabsloc
  | DIV_ASSIGN of cabsloc
  | DEFAULT of cabsloc
  | DEC of cabsloc
  | CONTINUE of cabsloc
  | CONSTANT of (constant0 * cabsloc)
  | CONST of cabsloc
  | COMMA of cabsloc
  | COLON of cabsloc
  | CHAR of cabsloc
  | CASE of cabsloc
  | C11_ATOMIC_STORE of cabsloc
  | C11_ATOMIC_LOAD of cabsloc
  | C11_ATOMIC_INIT of cabsloc
  | C11_ATOMIC_FETCH_KEY of cabsloc
  | C11_ATOMIC_EXCHANGE of cabsloc
  | C11_ATOMIC_COMPARE_EXCHANGE_WEAK of cabsloc
  | C11_ATOMIC_COMPARE_EXCHANGE_STRONG of cabsloc
  | BUILTIN_VA_ARG of cabsloc
  | BREAK of cabsloc
  | BOOL of cabsloc
  | BARES of cabsloc
  | BARBAR of cabsloc
  | BAR of cabsloc
  | BANG of cabsloc
  | ATOMIC of cabsloc
  | GENERIC of cabsloc
  | AND_ASSIGN of cabsloc
  | ANDAND of cabsloc
  | AND of cabsloc
  | ALIGNOF of cabsloc
  | ADD_ASSIGN of cabsloc
  
  (* Parser.mly specifics *)
  | VAR_NAME2  of (atom * cabsloc)
  | TYPEDEF_NAME2 of (atom * cabsloc)
  | OTHER_NAME of (atom * cabsloc)


 *)
