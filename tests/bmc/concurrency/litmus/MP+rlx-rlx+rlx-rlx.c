// MP+rlx-rlx+rlx-rlx
#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2;
  {-{ {
    atomic_store_explicit(&x, 1, memory_order_relaxed);
    atomic_store_explicit(&y, 1, memory_order_relaxed);
  } ||| {
    r1 = atomic_load_explicit(&y, memory_order_relaxed);
    if (r1 == 1)
      r2 = atomic_load_explicit(&x, memory_order_relaxed);
    else
      r2 = 2;
  } }-};
  __BMC_ASSUME(r1 == 1 && r2 == 0);
  // return r1 + 2 * r2;
}

