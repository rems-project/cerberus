/* 6.5.6#1 Additive operators, Syntax */
additive_expression:
| multiplicative_expression
    {$1}
| additive_expression PLUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.ADD, $1, $3)}
| additive_expression MINUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.SUB, $1, $3)}
;
