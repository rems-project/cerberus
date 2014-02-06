open Cabs0

type token = 
  | XOR_ASSIGN_ of cabsloc
  | WHILE_ of cabsloc
  | VOLATILE of cabsloc
  | VOID of cabsloc
  | VAR_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | UNSIGNED of cabsloc
  | UNKNOWN_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | UNION of cabsloc
  | TYPEDEF_NAME of (string * Pre_parser_aux.identifier_type ref * cabsloc)
  | TYPEDEF_ of cabsloc
  | TILDE of cabsloc
  | THREAD_LOCAL_ of cabsloc
  | SWITCH_ of cabsloc
  | SUB_ASSIGN_ of cabsloc
  | STRUCT of cabsloc
  | STRING_LITERAL of (string * cabsloc)
  | STATIC_ASSERT of cabsloc
  | STATIC_ of cabsloc
  | STAR of cabsloc
  | SLASH of cabsloc
  | SIZEOF of cabsloc
  | SIGNED of cabsloc
  | SHORT of cabsloc
  | SEMICOLON of cabsloc
  | RPAREN of cabsloc
  | RIGHT_ASSIGN of cabsloc
  | RIGHT of cabsloc
  | RETURN_ of cabsloc
  | RESTRICT of cabsloc
  | REGISTER_ of cabsloc
  | RBRACK of cabsloc
  | RBRACES of cabsloc
  | RBRACE of cabsloc
  | QUESTION_ of cabsloc
  | PTR_ of cabsloc
  | PLUS_ of cabsloc
  | PERCENT of cabsloc
  | OR_ASSIGN of cabsloc
  | OFFSETOF_ of cabsloc
  | NEQ of cabsloc
  | MUL_ASSIGN_ of cabsloc
  | MOD_ASSIGN_ of cabsloc
  | MINUS_ of cabsloc
  | LT_ of cabsloc
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
  | GT_ of cabsloc
  | GOTO_ of cabsloc
  | GEQ of cabsloc
  | FOR_ of cabsloc
  | FLOAT of cabsloc
  | EXTERN_ of cabsloc
  | EQEQ of cabsloc
  | EQ_ of cabsloc
  | EOF
  | ENUM of cabsloc
  | ELSE of cabsloc
  | ELLIPSIS of cabsloc
  | DOUBLE of cabsloc
  | DOT of cabsloc
  | DO of cabsloc
  | DIV_ASSIGN_ of cabsloc
  | DEFAULT_ of cabsloc
  | DEC of cabsloc
  | CONTINUE_ of cabsloc
  | CONSTANT_ of (constant1 * cabsloc)
  | CONST of cabsloc
  | COMMA_ of cabsloc
  | COLON of cabsloc
  | CHAR of cabsloc
  | CASE_ of cabsloc
  | C11_ATOMIC_STORE_ of cabsloc
  | C11_ATOMIC_LOAD_ of cabsloc
  | C11_ATOMIC_INIT_ of cabsloc
  | C11_ATOMIC_FETCH_KEY_ of cabsloc
  | C11_ATOMIC_EXCHANGE_ of cabsloc
  | C11_ATOMIC_COMPARE_EXCHANGE_WEAK_ of cabsloc
  | C11_ATOMIC_COMPARE_EXCHANGE_STRONG_ of cabsloc
  | BUILTIN_VA_ARG_ of cabsloc
  | BREAK_ of cabsloc
  | BOOL of cabsloc
  | BARES of cabsloc
  | BARBAR of cabsloc
  | BAR of cabsloc
  | BANG of cabsloc
  | AUTO_ of cabsloc
  | ATOMIC of cabsloc
  | AND_ASSIGN of cabsloc
  | ANDAND of cabsloc
  | AND_ of cabsloc
  | ALIGNOF_ of cabsloc
  | ADD_ASSIGN_ of cabsloc
  
  (* Parser.mly specifics *)
  | VAR_NAME2  of (atom * cabsloc)
  | TYPEDEF_NAME2 of (atom * cabsloc)
  | OTHER_NAME of (atom * cabsloc)
