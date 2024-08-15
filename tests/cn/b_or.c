int f(int x, int y)
    /*@ ensures return == x | y; @*/
{
    return x | y;
}
