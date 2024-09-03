int g(int *p, int *q)
/*@
 requires
    take P = Owned(p);
    take Q = Owned(q);
    ptr_eq(q, array_shift(p, 10i32));
ensures
    take P2 = Owned(p);
    P == P2;
    take Q2 = Owned(q);
    Q == Q2;
    return == -10i32;
@*/
{
  return p - q;
}

int f(int *p, int *q)
/*@
 requires
    !is_null(p);
    ptr_eq(q, array_shift(p, 10i32));
    take A = Alloc(p);
    A.base <= (u64) p;
    (u64) p <= (u64) q;
    (u64) q <= A.base + A.size;
ensures
    return == -10i32;
    take A2 = Alloc(p);
    A == A2;
@*/
{
  /*@ assert(allocs[(alloc_id)p] == A); @*/
  return p - q;
}

int main(void)
{
    int arr[11] = { 0 };
    f(&arr[0], &arr[10]);
    /*@ extract Owned<int>, 0u64; @*/
    /*@ extract Owned<int>, 10u64; @*/
    g(&arr[0], &arr[10]);
}
