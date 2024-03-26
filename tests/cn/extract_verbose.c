

int
f (int x, int *p, int *q)
/*@ requires take p_arr = each(u64 i; 0u64 <= i && i < 10u64) {Owned(array_shift(p, i))} @*/
/*@ requires take q_arr = each(u64 i; 0u64 <= i && i < 12u64) {Block<int>(array_shift(q, i))} @*/
/*@ ensures take p_arr2 = each(u64 i; 0u64 <= i && i < 10u64) {Owned(array_shift(p, i))} @*/
/*@ ensures take q_arr2 = each(u64 i; 0u64 <= i && i < 12u64) {Block<int>(array_shift(q, i))} @*/
{
  /*@ extract [verbose] Owned<int>, 1u64; @*/
  /*@ extract [verbose] Owned<int>, 1u64; @*/
  return 1;
}
