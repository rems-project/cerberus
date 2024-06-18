int f(int *p, int *q)
/*@
ensures
    return == 1i32;
@*/
{
    return p == q;
}

