void f(int *p)
/*@
requires
    !is_null(p);
ensures
    true;
@*/
{
    /*@ assert (has_alloc_id(0u64)); @*/
}

