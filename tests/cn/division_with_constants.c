/* Since the second operand that is a non-zero constant, there is
   no need to specify directly 10 != 0 && -10 != 0 since it is self-evident. */

int divide_by_ten (int x)
/*@ ensures return == x/10i32; @*/
{
    return x/10;
}

int divide_by_neg_ten (int x)
/*@ ensures return == x/-10i32; @*/
{
    return x/-10;
}

/* NOTE:
    If division is done between a positive and a negative int, result will be negative.
        Ex: ( x / -y ) = ( -x / y) = - ( x / y )

    If division is done between two negative ints or two positive, result will be positive.
        Ex: ( -x / -y ) = ( x / y )
*/

int division_diff_sign ()
/*@ ensures return == -2i32; @*/
{
    return 20 / -10;
}