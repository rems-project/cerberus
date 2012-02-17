type 'a set = 'a BatSet.t
type ('a, 'b) map = ('a, 'b) BatMap.t

type storage_class =
  | AUTO
  | STATIC

type int_base_type =
  | ICHAR
  | SHORT
  | INT
  | LONG
  | LONG_LONG

type int_type =
  | BOOL
  | SIGNED of int_base_type
  | UNSIGNED of int_base_type

type basic_type =
  | VOID
  | CHAR
  | INTEGER of int_type

type qualifiers = Cabs.qualifiers

type sequential_operator = Cabs.sequential_operator
type arithmetic_operator = Cabs.arithmetic_operator
type relational_operator = Cabs.relational_operator
type binary_operator = Cabs.binary_operator

type unary_operator =
  | MINUS
  | PLUS
  | BNOT
  | ADDRESS
  | INDIRECTION
  | POSTFIX_INCR
  | POSTFIX_DECR

type integer_constant = Cabs.integer_constant
type constant = Cabs.constant

type ctype =
  | BASE of qualifiers * basic_type
  (* TODO Need to convert integer constant to an actual value! Otherwise, we
     cannot compare types! *)
  | ARRAY of ctype * int
  | POINTER of qualifiers * ctype
  | FUNCTION of ctype * ctype list

type type_class =
  | Exp of ctype
  | Lvalue of ctype

type declaration = ctype * storage_class option

type ('id, 'e) definition = 'id * 'e

type ('id, 'e) expression =
  | UNARY of unary_operator * 'e
  | BINARY of binary_operator * 'e * 'e 
  | ASSIGN of arithmetic_operator option * 'e * 'e
  | QUESTION of 'e * 'e * 'e
  | CAST of ctype * 'e
  | CALL of 'e * 'e list
  | CONSTANT of Cabs.constant
  | VARIABLE of 'id
  | SIZEOF of ctype
  | ALIGNOF of ctype

type ('id, 'a) exp = 'a * ('id, ('id, 'a) exp) expression

(* Statements *)
type ('id, 'e, 's) statement =
  | SKIP
  | EXPRESSION of 'e
  | BLOCK of 'id list * 's list
  | IF of 'e * 's * 's
  | WHILE of 'e * 's
  | DO of 'e * 's
  | BREAK
  | CONTINUE
  | RETURN_VOID
  | RETURN_EXPRESSION of 'e
  | SWITCH of 'e * 's
  | CASE of Cabs.integer_constant * 's
  | DEFAULT of 's
  | LABEL of 'id * 's
  | GOTO of 'id
  | DECLARATION of ('id, 'e) definition list

type ('id, 'a_e, 'a_s) stmt =
    'a_s * ('id, ('id, 'a_e) exp, ('id, 'a_e, 'a_s) stmt) statement

type ('id, 'a_e, 'a_s) file = {
  main : 'id;
  id_map : ('id, declaration) map;
  globals : ('id * ('id, 'a_e) exp) list;
  function_map : ('id, ('id list * ('id, 'a_e, 'a_s) stmt)) map
}

type ('a_e, 'a_s) env = {
  symbol : CpSymbol.t;
  symbol_map : (CpSymbol.t, string) map;
  file : (CpSymbol.t, 'a_e, 'a_s) file
}

type 'a result =
  | Program of 'a
  | Undefined
  | Invalid
