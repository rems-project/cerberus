int live_owned_footprint(char *p, char *q)
/*@
 requires
    take P = Owned<int[11]>(array_shift<char>(p, -2i64));
    ptr_eq(q, array_shift<char>(p, 12i64));
ensures
    take P2 = Owned<int[11]>(array_shift<char>(p, -2i64));
    P == P2;
    return == 0i32;
@*/
{
  /*@ extract Owned<int>, 7u64; @*/
  // NOTE: neither argument needs to be in the footprint of the Owned
  // The bounds check for the allocation are done separately to the resource
  // lookup
  return q < p;
}

// Here, only one ownership is required to establish the that the allocation is
// live, but both are required to ensure that the bounds check succeeds
int live_owned_both(int *p, int *q)
/*@
 requires
    take P = Owned(p);
    take Q = Owned(q);
    (u64) p < (u64) q;
    ptr_eq(q, array_shift(p, 10i32));
ensures
    take P2 = Owned(p);
    P == P2;
    take Q2 = Owned(q);
    Q == Q2;
    return == 0i32;
@*/
{
  return p > q;
}

int live_owned_one(int *p, int *q)
/*@
 requires
    take P = Owned(p);
    ptr_eq(q, array_shift(p, 10i32));
    let A = allocs[(alloc_id)p];
    (u64) p <= (u64) q;
    (u64) q <= A.base + A.size;
ensures
    take P2 = Owned(p);
    P == P2;
    return == 1i32;
@*/
{
  return p <= q;
}

int live_alloc(int *p, int *q)
/*@
 requires
    !is_null(p);
    ptr_eq(q, array_shift(p, 10i32));
    take A = Alloc(p);
    A.base <= (u64) p;
    (u64) p <= (u64) q;
    (u64) q <= A.base + A.size;
ensures
    return == 0i32;
    take A2 = Alloc(p);
    A == A2;
@*/
{
  /*@ assert(allocs[(alloc_id)p] == A); @*/
  return p >= q;
}

int main(void)
{
    int arr[11] = { 0 };
    live_alloc(&arr[0], &arr[10]);
    /*@ extract Owned<int>, 0u64; @*/
    /*@ extract Owned<int>, 10u64; @*/
    live_owned_one(&arr[0], &arr[10]);
    live_owned_both(&arr[0], &arr[10]);
    char *p = (char*) arr;
    live_owned_footprint(p + 2, p + 14);
}
