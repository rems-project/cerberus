// RMW-weak-unequal
/* The weak compare_exchange will always fail if the compared values
are not equal. Hence, the value of x will still be 0 at the end of the
execution and the value of y will be 0. An exhaustive execution will
therefore only return 0. */
#include <stdatomic.h>
int main(void) {
  _Atomic(int) x = 0;
  int y = 1;
  int r1 = atomic_compare_exchange_weak_explicit(
                &x, &y, 1, memory_order_seq_cst, memory_order_seq_cst);

  int a = atomic_load_explicit(&x, memory_order_relaxed);
  assert(y == 0 && r1 == 0 && a == 0);
  // return a + 3 * (y + 3 * r1);
}
