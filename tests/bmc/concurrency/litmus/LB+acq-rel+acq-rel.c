// LB+acq_rel+acq_rel
// Load Buffering, with acquire/release pairs
// The values of z1 and z2 cannot both be 1. They can be both 0, or one of them can be 1.
// An exhaustive execution of this program should therefore return the values 0, 1 and 2.
#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2;
  {-{ {
    r1 = atomic_load_explicit(&x, memory_order_acquire);
    atomic_store_explicit(&y, 1, memory_order_release);
  } ||| {
    r2 = atomic_load_explicit(&y, memory_order_acquire);
    atomic_store_explicit(&x, 1, memory_order_release);
  } }-};
  __BMC_ASSUME(r1 == 1 && r2 == 1);
  return z1 + (2 * z2);
  return 0;
}

