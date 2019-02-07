/*The weak compare_exchange can always fail, even if the compared
values are equal. If it succeeds then the value of x will be 1, and
the value of y will still be 0. Otherwise, the values of x and y will
still be 0. An exhaustive execution will therefore return 5 and 0 */

#include <stdatomic.h>
int main(void) {
  _Atomic(int) x = 0;
  int y = 0;
  int r1, a;
  r1 = atomic_compare_exchange_weak_explicit(
    &x, &y, 1, memory_order_seq_cst, memory_order_seq_cst);
  a = atomic_load_explicit(&x, memory_order_relaxed);
  return a + 2 * y + 4 * r1;
}

