//  C-LB+o-mb-o+o-rmb-o.c
#include "linux.h"
int main() {
  int x = 0, y = 0;
  int r1, r3;
  {-{ { r1 = READ_ONCE(x);
        smp_mb();
        WRITE_ONCE(y, 1);
      }
  ||| { r3 = READ_ONCE(y); 
        smp_rmb();
        WRITE_ONCE(x, 1); 
      }
  }-}
  __BMC_ASSUME(r1 == 1 && r3 == 1);
  return r1 + 2 * r3;
}
