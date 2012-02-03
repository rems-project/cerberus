/* 6.5.4#1 Cast operators, Syntax */
cast_expression:
| unary_expression
    {$1}
| LPAREN type_name RPAREN cast_expression
    {C.CAST ($2, $4)}
;
