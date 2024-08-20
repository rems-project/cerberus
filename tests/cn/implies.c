int identity(int x)
{
    int y = x;
    /*@ assert((x == 0i32) implies (y == 0i32));@*/
    return y;
}