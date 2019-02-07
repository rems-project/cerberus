// LISA2R2G
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA2R2G.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0, x3 = 0;
  int r1, t0_r2, t2_r2, r3;
  {-{ {
    rcu_read_lock();
    t0_r2 = READ_ONCE(x0);
    WRITE_ONCE(x1, 1);
    rcu_read_unlock();
  } ||| {
    r1 = READ_ONCE(x1);
    synchronize_rcu();
    WRITE_ONCE(x2, 1);
  } ||| {
    t2_r2 = READ_ONCE(x2);
    synchronize_rcu();
    WRITE_ONCE(x3, 1);
  } ||| {
    rcu_read_lock();
    r3 = READ_ONCE(x3);
    WRITE_ONCE(x0, 1);
    rcu_read_unlock();
  } }-};
  assert(!(r1 == 1 && t2_r2 == 1 && r3 == 1 && t0_r2 == 1));
  return r1 + 2 * (t2_r2 + 2 * (r3 + 2 * t0_r2));
}
