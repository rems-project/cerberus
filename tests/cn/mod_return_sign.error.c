/* Modulo can be done with Integers of different signs and sizes
   but think about the return type carefully. */

// fails because it should return unsigned int
int different_sign (int x, unsigned int y)
/*@ requires y != 0u32;
    ensures return == x % y; @*/
{
    return x % y;
}