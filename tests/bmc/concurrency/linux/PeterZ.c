#include "linux.h"

int main() {
  int x = 0, y = 0, z = 0;
  int r1, r2, r3;
  {-{ {
        WRITE_ONCE(x, 1);
        smp_mb();
        r1 = READ_ONCE(y);
      }
  ||| {
        WRITE_ONCE(y, 1);
        smp_store_release(&z, 1);
      }
  ||| {
        r2 = smp_load_acquire(&z);
        smp_mb();
        r3 = READ_ONCE(x); 
      }
  }-}
  assert (!(r1 == 0 && r2 == 1 && r3 == 0));
  return r1 + 2 * r2 + 4 * r3;
}
