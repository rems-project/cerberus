/* Must specify that the second operand is not equal than zero

   In our case, y is the second operand which means we must
   specify that y != 0i32. The function will work with this pre-condition. */

int mod (int x, int y)
/*@ requires y != 0i32;
    ensures return == x % y; @*/
{
    return x % y;
}