/* RCU-deferred-free with a broken reader */
#include "linux.h"
int main() {
  int x = 0, y = 0;
  int r1, r2;
  {-{ {
    WRITE_ONCE(x, 1);
    synchronize_rcu();
    WRITE_ONCE(y, 1);
  } ||| {
    r1 = READ_ONCE(x);
    r2 = READ_ONCE(y);
  } }-}
  __BMC_ASSUME(r1 == 0 && r2 == 1);
  return r1 + 2 * r2;
}
