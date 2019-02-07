// LB+rlx-data-rlx+rlx-data-rlx_initialised
#include <stdatomic.h>
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1 = 0, r2 = 0;
  {-{ {
    r1 = atomic_load_explicit(&x, memory_order_relaxed);
    atomic_store_explicit(&y, r1, memory_order_relaxed); }
  ||| {
    r2 = atomic_load_explicit(&y, memory_order_relaxed);
    atomic_store_explicit(&x, r2, memory_order_relaxed);
  } }-};
#if __memory_model_c11__
  __BMC_ASSUME((r1 == 1 && r2 == 1));
#elif __memory_model_rc11__
  assert(!(r1 == 1 && r2 == 1));
#endif
  // return r1 + (2 * r2);
}
