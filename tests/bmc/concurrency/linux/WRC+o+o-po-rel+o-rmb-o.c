#include "linux.h"

int main() {
  int x = 0, y = 0;
  int r1, r2, r3;
  {-{
    WRITE_ONCE(x, 1);
  ||| {
    r1 = READ_ONCE(x);
    smp_store_release(&y, 1);
  } ||| {
    r2 = READ_ONCE(y);
    smp_rmb();
    r3 = READ_ONCE(x);
  } }-}
  assert(!(r1 == 1 && r2 == 1 && r3 == 0));
  return r1 + 2 * r2 + 4 * r3;
}
