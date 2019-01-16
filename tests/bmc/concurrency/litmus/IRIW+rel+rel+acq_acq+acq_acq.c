// IRIW with release/acquire
// The reading threads do not have to see the writes to x and y in the same order.

#include <stdatomic.h>

int main(void) {
  _Atomic(int) x = 0; 
  _Atomic(int) y = 0;
  int z1; int z2; int z3; int z4;
  {-{ atomic_store_explicit(&x, 1, memory_order_release);
  ||| atomic_store_explicit(&y, 1, memory_order_release);
  ||| { z1=atomic_load_explicit(&x, memory_order_acquire);
        z2=atomic_load_explicit(&y, memory_order_acquire); }
  ||| { z3=atomic_load_explicit(&y, memory_order_acquire);
        z4=atomic_load_explicit(&x, memory_order_acquire); }
  }-};
  return (z1 + 2 * (z2 + 2 * (z3 + 2 * z4)));
}

