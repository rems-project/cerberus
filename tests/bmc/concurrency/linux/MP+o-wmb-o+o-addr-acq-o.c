#include "linux.h"

int main() {
  int x = 0, y = 0, z = 0;
  int r1, r2, r3;
  {-{ { WRITE_ONCE(x, 1);
        smp_wmb();
        WRITE_ONCE(y, 1);
      }
  ||| { r1 = READ_ONCE(y); 
        r3 = smp_load_acquire(&z + r1 - r1);
        r2 = READ_ONCE(x); 
      }
  }-}
  assert(!(r1 == 1 && r2 == 0));
  return r1 + 2 * r2;
}
