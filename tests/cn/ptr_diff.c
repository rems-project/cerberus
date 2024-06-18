int f(int *p, int *q)
/*@
 requires
    !is_null(p);
    ptr_eq(q, array_shift(p, 10i32));
ensures
    return == -10i32;
@*/
{
  return p - q; // intentionally p - q = -10;
}

int main(void)
{
    int arr[11] = { 0 };
    f(&arr[0], &arr[10]);
}
