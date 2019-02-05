#include "linux.h"

int main() {
  int x = 0, y = 0;
  int r1, r2;
  {-{ { WRITE_ONCE(x, 1);
        smp_wmb();
        WRITE_ONCE(y, 1);
      }
  ||| { r1 = READ_ONCE(y); 
        smp_rmb();
        r2 = READ_ONCE(x); 
      }
  }-}
  // 2 (r1 == 0 && r2 == 1) forbidden
  return r1 + 2 * r2;
}
