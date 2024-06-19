

int
f (int x, int *p, int *q)
/*@ requires take p_arr = each(u64 i; 0u64 <= i && i < 10u64) {Owned(array_shift(p, i))};
             take q_arr = each(u64 i; 0u64 <= i && i < 12u64) {Block<int>(array_shift(q, i))};
    ensures take p_arr2 = each(u64 i; 0u64 <= i && i < 10u64) {Owned(array_shift(p, i))};
            take q_arr2 = each(u64 i; 0u64 <= i && i < 12u64) {Block<int>(array_shift(q, i))}; @*/
{
  /*@ extract Owned<int>, 1; @*/
  /*@ extract Owned<int>, 1; @*/
  /*@ extract Owned<int>, 1u64; @*/
  /*@ extract Owned<int>, 1u64; @*/
  /*@ extract Owned<int>, 12; @*/
  return 1;
}

int main(void)
/*@ trusted; @*/
{
  int p[5] = {1, 2, 3, 4, 5};
  int q[5] = {6, 7, 8, 9, 10};
  f(42, p, q);
}
