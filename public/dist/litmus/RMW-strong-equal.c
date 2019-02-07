/* The strong compare_exchange will always succeed if the compared
values are equal. Hence, the value of x will be 1 at the end of the
execution and the value of y still 0. An exhaustive execution will
therefore only return 5. */
#include <stdatomic.h>
int main(void) {
  _Atomic(int) x = 0;
  int y = 0;
  int r1, a;
  r1 = atomic_compare_exchange_strong_explicit(
    &x, &y, 1, memory_order_seq_cst, memory_order_seq_cst);
  a = atomic_load_explicit(&x, memory_order_relaxed);
  return a + 2 * y + 4 * r1;
}
