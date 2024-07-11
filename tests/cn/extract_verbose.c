

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
  int p[10] = {1, 2, 3, 4, 5, 6, 9, 10, 11, 12};
  int q[12] = {1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5};
  f(42, p, q);
}
