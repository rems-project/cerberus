#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2;
  {-{ {
    r1 = atomic_load_explicit(&x, memory_order_relaxed);
    if (r1 == 1) {
      atomic_store_explicit(&y, r1, memory_order_relaxed);
    }
  } ||| {
    r2 = atomic_load_explicit(&y, memory_order_relaxed);
    if (r2 == 1) {
      atomic_store_explicit(&x, r2, memory_order_relaxed);
    }
  } }-};
  __BMC_ASSUME(r1 == 1 && r2 == 1); // for C11
  // assert(!(r1 == 1 && r2 == 1)); // for RC11
  return r1 + 2 * r2;
}

