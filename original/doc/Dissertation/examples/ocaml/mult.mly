/* 6.5.5#1 Multiplicative operators, Syntax */
multiplicative_expression:
| cast_expression
    {$1}
| multiplicative_expression STAR cast_expression
    {C.BINARY (C.ARITHMETIC C.MUL, $1, $3)}
| multiplicative_expression SLASH cast_expression
    {C.BINARY (C.ARITHMETIC C.DIV, $1, $3)}
| multiplicative_expression PERCENT cast_expression
    {C.BINARY (C.ARITHMETIC C.MOD, $1, $3)}
;
