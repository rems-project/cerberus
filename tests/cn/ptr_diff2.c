int* f(int *p)
/*@
requires
    has_alloc_id(p);
    let A = allocs[(alloc_id)p];
    A.base <= (u64) p - 4u64;
    (u64) p - 4u64 < (u64) p;
    (u64) p <= A.base + A.size;
ensures
    ptr_eq(return, array_shift(p, -1i32));
@*/
{
  return p - 1;
}

int main(void)
{
    int arr[2] = { 0 };
    f(arr + 1);
}
