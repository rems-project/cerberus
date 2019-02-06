#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int z1 = 0, z2 = 0;
  {-{ { z1 = atomic_load_explicit(&x, memory_order_relaxed);
        atomic_store_explicit(&y, z1, memory_order_relaxed); }
  ||| { z2 = atomic_load_explicit(&y, memory_order_relaxed);
        atomic_store_explicit(&x, z2, memory_order_relaxed); }  }-};
  __BMC_ASSUME((z1 == 1 && z2 == 1)); // for C11
  // assert(!(z1 == 1 && z2 == 1)); // for RC11
  return z1 + (2 * z2);
}
