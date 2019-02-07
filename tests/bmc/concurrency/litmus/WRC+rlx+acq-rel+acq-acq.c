// WRC+rel+acq-rel+acq-acq
#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2, r3;
  {-{ {
    atomic_store_explicit(&x, 1, memory_order_relaxed);
  } ||| {
    r1 = atomic_load_explicit(&x, memory_order_acquire);
    atomic_store_explicit(&y, 1, memory_order_release);
  } ||| {
    r2 = atomic_load_explicit(&y, memory_order_acquire);
    r3 = atomic_load_explicit(&x, memory_order_acquire);
  } }-}
  assert(!(r1 == 1 && r2 == 1 && r3 == 0));
  return r1 + 2 * (r2 + 2 * r3);
}
