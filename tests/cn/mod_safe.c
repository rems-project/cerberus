/* NOTE:
    You do not need to specify the second operand does not equal 0,
    if you and only if your function handles case where it is equal to zero. @*/

int safe_mod (int x, int y)
/*@ ensures return == ( y == 0i32 ? ( 0i32 ) : (x % y)); @*/
{
    if (y == 0)
    {
        return 0;
    }
    else
    {
        return x % y;
    }
}