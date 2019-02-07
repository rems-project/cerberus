// MP+na-rel+acq-na
// Message Passing, of data held in non-atomic x, with release/acquire synchronisation on y.
// If the value of r1 is 1, then the value of r2 should also be 1.
// An exhaustive execution of this program should therefore return the value 1 and 2, but not 0.
#include <stdatomic.h>
int main() {
  int x = 0;
  _Atomic(int) y = 0;
  int r1, r2;
  {-{ {
    x = 1;
    atomic_store_explicit(&y, 1, memory_order_release);
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

