// LISA2Rt2G
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA2Rt2G.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0, x3 = 0, x4 = 0;
  int r1, r2, r3, r4;
  {-{ {
    rcu_read_lock();
    WRITE_ONCE(x0, 1);
    WRITE_ONCE(x1, 1);
    rcu_read_unlock();
    rcu_read_lock();
    WRITE_ONCE(x2, 1);
    WRITE_ONCE(x3, 1);
    rcu_read_unlock();
  } ||| {
    r1 = READ_ONCE(x1);
    synchronize_rcu();
    r2 = READ_ONCE(x0);
  } ||| {
    r3 = READ_ONCE(x3);
    synchronize_rcu();
    r4 = READ_ONCE(x4);
  } }-};
  assert(!(r1 == 1 && r2 == 0 && r3 == 1 && r4 == 0));
  // return r1 + 2 * (r2 + 2 * (r3 + 2 * r4));
}
