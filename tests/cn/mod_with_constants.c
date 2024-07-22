/* Since the second operand is constant that is not equal to zero,
   You can execute the division with no worries for Modulo By Zero */

int x_mod_three (int x)
/*@ ensures return == x % 3i32; @*/
{
    return x % 3;
}

int x_mod_neg_three (int x)
/*@ ensures return == x % -3i32; @*/
{
    return x % -3;
}

/* NOTE:
    If the first operand is positive or both operands are positive, the result will be positive.
            Ex: ( x % y ) =  ( x % - y )

    If the first operand is negative or both operands are negative, the result will be negative.
            Ex: ( -x % y ) = ( -x % -y ) = - ( x % y )
*/

int mod_first_operand_neg ()
/*@  ensures return == -2i32; @*/
{
    return -5 % 3;
}


