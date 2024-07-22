/* Modulo can be done with Integers of different signs and sizes
   but think about the return type carefully. */

// fails because it should return a long
int different_size(int x, long y)
/*@ requires y != 0i64;
    ensures return == x % (i32)y; @*/
{
    return x % y;
}