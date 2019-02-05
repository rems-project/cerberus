#include "linux.h"

int main() {
  int x = 0, y = 0;
  int r1, r2;
  {-{ { WRITE_ONCE(x, 1);
        smp_mb();
        r1 = READ_ONCE(y);
      }
  ||| { WRITE_ONCE(y, 1);
        smp_mb();
        r2 = READ_ONCE(x);
      }
  }-}
  // 0 (r1 == 0 && r2 == 0) forbidden
  return r1 + 2* r2;
}
