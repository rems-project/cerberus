int f(int *p)
/*@ requires take vs = each(i32 i; i == -1i32) { RW<int>(array_shift(p,i)) };
    ensures take ws = each(i32 i; i == -1i32) { RW<int>(array_shift(p,i)) };
@*/
{
  /*@ focus Owned<int>, -1i32; @*/
  return p[-1];
}

int main(void)
/*@ trusted; @*/
{
  int p[5] = {1, 2, 3, 4, 5};
  int r = f(p);
}
