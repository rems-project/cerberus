#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2;
  {-{ {
    r1 = atomic_load_explicit(&x, memory_order_relaxed);
    atomic_store_explicit(&y, 1, memory_order_relaxed);
  } ||| {
    r2 = atomic_load_explicit(&y, memory_order_relaxed);
    atomic_store_explicit(&x, 1, memory_order_relaxed);
  } }-};
  __BMC_ASSUME(r1 == 1 && r2 == 1);
  return r1 + (2 * r2);
}

