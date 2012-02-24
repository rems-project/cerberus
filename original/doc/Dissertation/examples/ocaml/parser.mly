/* 6.5.4#1 Cast operators, Syntax */
cast_expression:
| unary_expression
    {$1}
| LPAREN type_name RPAREN cast_expression
    {C.CAST ($2, $4)}
;

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

/* 6.5.6#1 Additive operators, Syntax */
additive_expression:
| multiplicative_expression
    {$1}
| additive_expression PLUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.ADD, $1, $3)}
| additive_expression MINUS multiplicative_expression
    {C.BINARY (C.ARITHMETIC C.SUB, $1, $3)}
;
