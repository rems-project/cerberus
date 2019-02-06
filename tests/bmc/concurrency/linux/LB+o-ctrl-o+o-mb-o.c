#include "linux.h"
int main() {
  int x = 0, y = 0;
  int r1, r2;
  {-{ {
    r1 = READ_ONCE(x);
    if (r1 == 1) {
      WRITE_ONCE(y, 1);
    }
  } ||| {
    r2 = READ_ONCE(y);
    smp_mb();
    WRITE_ONCE(x, 1);
  } }-}
  assert(!(r1 == 1 && r2 == 1));
  return r1 + 2 * r2;
}
