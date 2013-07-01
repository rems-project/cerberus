module Ail where

type Id = String

data StorageDuration
  = STATIC
  | THREAD
  | AUTOMATIC
  | ALLOCATED

data IntBaseType
  = ICHAR
  | SHORT
  | INT
  | LONG
  | LONG_LONG

data IntType
  = BOOL
  | SIGNED IntBaseType
  | UNSIGNED IntBaseType

data BasicType
  = CHAR
  | INTEGER IntType

data Qualifiers
  = CONST
  | RESTRICT
  | VOLATILE
  | ATOMIC

data ArithmeticOperator
  = MUL | DIV | MOD
  | ADD | SUB
  | SHL | SHR
  | BAND
  | BOR
  | XOR

data BinaryOperator
  = ARITHMETIC ArithmeticOperator
  | COMMA
  | AND
  | OR
  | LT | GT | LE | GE
  | EQ | NE

data UnaryOperator
  = MINUS
  | PLUS
  | BNOT
  | ADDRESS
  | INDIRECTION
  | POSTFIX_INCR
  | POSTFIX_DECR

data IntegerSuffix
  = SUFFIX_UNSIGNED
  | SUFFIX_UNSIGNED_LONG
  | SUFFIX_UNSIGNED_LONG_LONG
  | SUFFIX_LONG
  | SUFFIX_LONG_LONG
type IntegerConstant = (Integer, Maybe IntegerSuffix)
data Constant
  = CONST_INT IntegerConstant
  | CONST_ENUM String

data Ctype
  = VOID Qualifiers
  | BASIC Qualifiers BasicType
  | ARRAY Ctype Integer
  | POINTER Qualifiers Ctype
  | FUNCTION Ctype [Ctype]

data TypeClass
  = T_EXP Ctype
  | T_LVALUE Ctype

type Declaration = (Ctype, Maybe StorageDuration)

data Expression
  = UNARY UnaryOperator Expression
  | BINARY BinaryOperator Expression Expression
  | ASSIGN (Maybe ArithmeticOperator) Expression Expression
  | QUESTION Expression Expression Expression
  | CAST Ctype Expression
  | CALL Expression [Expression]
  | MEMBEROF Expression Id
  | MEMBEROFPTR Expression Id
  | CONSTANT Constant
  | VARIABLE Id
  | SIZEOF Ctype
  | ALIGNOF Ctype

type Definition = (Id, Expression)

data Statement
  = SKIP
  | EXPRESSION Expression
  | BLOCK [Id] [Statement]
  | IF Expression Statement Statement
  | WHILE Expression Statement
  | DO Expression Statement
  | BREAK
  | CONTINUE
  | RETURN_VOID
  | RETURN_EXPRESSION Expression
  | SWITCH Expression Statement
  | CASE IntegerConstant Statement
  | DEFAULT Statement
  | LABEL Id Statement
  | GOTO Id
  | DECLARATION [Definition]

{-
type 'a file = <|
  main : id;
  id_map : (id, declaration) map;
  globals : (id * Expression_l a) list;
  fn_map : (id, (id list * 'a statement_l)) map
|>

type 'a env = <|
  symbol : id;
  symbol_map : (id, string) map;
  file : 'a file
|>
-}