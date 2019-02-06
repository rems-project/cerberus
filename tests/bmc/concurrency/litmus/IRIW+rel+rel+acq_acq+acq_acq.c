// IRIW with release/acquire
// The reading threads do not have to see the writes to x and y in the same order.
#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2, r3, r4;
  {-{
    atomic_store_explicit(&x, 1, memory_order_release);
  |||
    atomic_store_explicit(&y, 1, memory_order_release);
  ||| {
    r1 = atomic_load_explicit(&x, memory_order_acquire);
    r2 = atomic_load_explicit(&y, memory_order_acquire);
  } ||| {
    r3 = atomic_load_explicit(&y, memory_order_acquire);
    r4 = atomic_load_explicit(&x, memory_order_acquire);
  } }-};
  __BMC_ASSUME(r1 == 1 && r2 == 0 && r3 == 1 && r4 == 0);
  return (r1 + 2 * (r2 + 2 * (r3 + 2 * r4)));
}

