int f(int *p, int *q)
/*@
ensures
    return == 0i32;
@*/
{
    return p == q;
}

