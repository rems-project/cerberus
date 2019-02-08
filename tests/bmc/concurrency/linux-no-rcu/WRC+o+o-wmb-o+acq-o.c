#include "linux.h"
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2, r3;
  {-{ {
    WRITE_ONCE(x, 1);
  } ||| {
    r1 = READ_ONCE(x);
    smp_wmb();
    WRITE_ONCE(y, 1);
  } ||| {
    r2 = smp_load_acquire(&y);
    smp_mb();
    r3 = READ_ONCE(x);
  } }-}
  __BMC_ASSUME(r1 == 1 && r2 == 1 && r3 == 0);
  // return r1 + 2 * r2 + 4 * r3;
}
