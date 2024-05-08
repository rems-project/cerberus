/*@

function (i8) negate_var() {
    let x = 5i8;
    -x
}

function (i8) negate_paren() {
    -(127i8 + 2i8)
}
function (integer) negate_arith() {
    5 + -9
}
@*/
void check_simplify()
{
    /*@ assert(negate_paren() == 127i8); @*/
}
