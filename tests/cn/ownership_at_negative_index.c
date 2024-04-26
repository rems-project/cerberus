int f(int *p)
/*@ requires take vs = each(i32 i; i == -1i32) { Owned<int>(array_shift(p,i)) };
    ensures take ws = each(i32 i; i == -1i32) { Owned<int>(array_shift(p,i)) };
@*/
{
  /*@ extract Owned<int>, -1i32; @*/
  return p[-1];
}
