// LISA3Rqq1G
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA3Rqq1G.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0, x3 = 0, v0 = 0;
  int r1, t2_r2, r3, t0_r2;
  {-{ {
    rcu_read_lock();
    r2 = READ_ONCE(x0);
    WRITE_ONCE(x1, 1);
    rcu_read_unlock();
  } ||| {
    r1 = READ_ONCE(x1);
    synchronize_rcu();
    WRITE_ONCE(x2, 1);
    smp_store_release(&v0, 1);
  } ||| {
    rcu_read_lock();
    r2 = READ_ONCE(x2);
    smp_store_release(x3, 1);
    rcu_read_unlock();
  } ||| {
    rcu_read_lock();
    r4 = smp_load_acquire(&x0);
    r3 = READ_ONCE(x3);
    WRITE_ONCE(x0, 1);
    rcu_read_unlock();
  } }-};
  assert(!(r1 == 1 && t2_r2 == 1 && r3 == 1 && r4 == 1 && t0_r2 == 0));
  return r1 + 2 * (t2_r2 + 2 * (r3 + 2 * (r4 + 2 * t0_r2)));
}
