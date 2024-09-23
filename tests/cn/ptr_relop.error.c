int live_owned_footprint(char *p, char *q)
/*@
 requires
    take P = Owned<int[11]>(array_shift<char>(p, -2i64));
    ptr_eq(q, array_shift<char>(p, 12i64));
ensures
    take P2 = Owned<int[11]>(array_shift<char>(p, -2i64));
    P == P2;
    return == 1i32;
@*/
{
  // will fail without -- /*@ extract Owned<int>, 7u64; @*/
  return q > p;
}

int main(void)
{
    int arr[11] = { 0 };
    char *p = (char*) arr;
    live_owned_footprint(p + 2, p + 14);
}
