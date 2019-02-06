// SB+rel_acq+rel_acq
// Store Buffering (or Dekker's), with release-acquire pairs
// The reads can both see 0 in the same execution. 
// An exhaustive execution of this program should therefore return the values 0, 1, 2, 3.

#include <stdatomic.h>
int main() {
  _Atomic(int) x=0, y=0; 
  int z1, z2;
  {-{ { atomic_store_explicit(&y, 1, memory_order_release);
        z1 = atomic_load_explicit(&x, memory_order_acquire); }
  ||| { atomic_store_explicit(&x, 1, memory_order_release);
        z2 = atomic_load_explicit(&y, memory_order_acquire); }  }-};
  int ret = z1 + (2 * z2);
  assert (ret != 2);
  return ret;
}

