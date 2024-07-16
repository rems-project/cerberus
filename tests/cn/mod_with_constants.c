/* Since the second operand is constant that is not equal to zero,
   You can execute the division with no worries for a modulo by zero
*/

int x_mod_three (int x)
/*@ ensures return == (x % 3i32); @*/
{
    return x % 3;
}

int x_mod_neg_three (int x)
/*@ ensures return == (x % -3i32); @*/
{
    return x % -3;
}

// NOTE: Not sure if negative second operand produces correct values
int five_mod_neg_three ()
/*@  ensures return == -1i32;  @*/  //Should == -2i32
{
    return 5 % -3;
}


/* However, since you are executing the modulo with variable for a second operand,
   you will indeed to need to require that its value is not 0.   */

int six_mod_x (int x)
/*@ requires x != 0i32;
    ensures return == 6i32 % x; 
@*/
{
    return 6 % x;
}