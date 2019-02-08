// ESOP 2015
#include <stdatomic.h>
int main() {
#if __memory_model_c11__
  _Atomic(int) x = 0, y = 0;
  int a[1] = {0};
  int r1, r2, r3;
  {-{ {
    r1 = atomic_load_explicit(&x, memory_order_relaxed);
    r3 = a[r1];
    atomic_store_explicit(&y, 2, memory_order_relaxed);
  } ||| {
    r2 = atomic_load_explicit(&y, memory_order_relaxed);
    atomic_store_explicit(&x, r2, memory_order_relaxed);
  } }-};
#elif __memory_model_rc11__
  // hack for the test harness
  int x;
  {-{ x = 1; ||| x = 1; }-};
#endif
}
