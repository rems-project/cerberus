#include "linux.h"
int main() {
  _Atomic(int) x = 0, y = 0;
  int r1, r2, r3;
  {-{ {
    WRITE_ONCE(x, 1);
  } ||| {
    r1 = READ_ONCE(x);
    smp_mb();
    r2 = READ_ONCE(y);
  } ||| {
    WRITE_ONCE(y, 1);
    smp_mb();
    r3 = READ_ONCE(x);
  } }-}
  assert(!(r1 == 1 && r2 == 0 && r3 == 0));
  // return r1 + 2 * r2 + 4 * r3;
}
