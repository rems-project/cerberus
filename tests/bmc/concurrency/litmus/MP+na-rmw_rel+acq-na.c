// MP+na-rmw_rel+acq-na
#include <stdatomic.h>
int main() {
  int x = 0, v = 0;
  _Atomic(int) y = 0;
  int r1, r2;
  {-{ {
    x = 1;
    atomic_compare_exchange_strong_explicit(&y, &v, 1, memory_order_release, memory_order_relaxed);
  } ||| {
    r1 = atomic_load_explicit(&y, memory_order_acquire);
    if (r1 == 1)
      r2 = x;
    else
      r2 = 2;
  } }-};
  assert(!(r1 == 1 && r2 == 0));
  // return r1 + 2 * r2;
}

