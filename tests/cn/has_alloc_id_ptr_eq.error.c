int f(int *p, int *q)
/*@
requires
    has_alloc_id(p);
    has_alloc_id(q);
ensures
    return == 1i32;
@*/
{
    return p == q;
}

