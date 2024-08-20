/* Division by zero is an undefined behavior.
   Must specify that the second operand is not equal to zero */

int division (int x, int y)
/*@ requires y != 0i32;
    ensures return == x/y; @*/
{
    return x / y;
}