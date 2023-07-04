
Inductive arithmeticOperator : Type :=
(* STD Â§6.5.5 Multiplicative operators *)
| Mul: arithmeticOperator
| Div: arithmeticOperator
| Mod: arithmeticOperator
(* STD Â§6.5.6 Additive operators *)
| Add: arithmeticOperator
| Sub: arithmeticOperator
(* STD Â§6.5.7 Bitwise shift operators *)
| Shl: arithmeticOperator
| Shr: arithmeticOperator
(* STD Â§6.5.10 Bitwise AND operator *)
| Band: arithmeticOperator
(* STD Â§6.5.11 Bitwise exclusive OR operator *)
| Bxor: arithmeticOperator
(* STD Â§6.5.12 Bitwise inclusive OR operator *)
| Bor: arithmeticOperator.

Inductive unaryOperator : Type :=
| Plus: unaryOperator
| Minus: unaryOperator
| Bnot: unaryOperator
| Address: unaryOperator
| Indirection: unaryOperator
| PostfixIncr: unaryOperator  (*r Note: Appears prefix in concrete syntax. *)
| PostfixDecr: unaryOperator.

Inductive binaryOperator : Type :=   (*r Group of operators also used for assignments *)
| Arithmetic:  arithmeticOperator  -> binaryOperator  (*r 6.5.17 Comma operator *)
| Comma: binaryOperator  (*r 6.5.13 Logical AND operator *)
| And: binaryOperator  (*r 6.5.14 Logical OR operator *)
| Or: binaryOperator  (*r 6.5.8 Relational operators *)
| Lt: binaryOperator
| Gt: binaryOperator
| Le: binaryOperator
| Ge: binaryOperator  (*r 6.5.9 Equality operators *)
| Eq: binaryOperator
| Ne: binaryOperator.
