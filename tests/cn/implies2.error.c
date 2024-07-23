int identity(int x) 
{
    int y = x;
    /*@ assert((x == 0i32) implies (y == 1i32));@*/
    return y;
}