// This will fail if/when funcptrs are added as a separate constructor for the
// SMT representation of pointers
void f(int *p)
/*@
requires
    !is_null(p);
ensures
    true;
@*/
{
    /*@ assert (has_alloc_id(p)); @*/
}

// This will fail if/when funcptrs are added as a separate constructor for the
// SMT representation of pointers
void g(int *p)
/*@
requires
    has_alloc_id(p);
ensures
    true;
@*/
{
    /*@ assert (!is_null(p)); @*/
}

int main()
{
    int x = 0;
    f(&x);
    g(&x);
}
