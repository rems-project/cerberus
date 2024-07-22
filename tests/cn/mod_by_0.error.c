/* Fails because it doesn't require the second operand to be non-zero. */

int mod (int x, int y)
/*@  ensures return == x % y; @*/
{
    return x % y;
}