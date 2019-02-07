// LISA2qR1G
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA2qR1G.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0;
  int r1, t0_r2, t2_r2;
  {-{ {
    rcu_read_lock();
    r2 = READ_ONCE(x0);
    WRITE(x1, 1);
    rcu_read_unlock();
  } ||| {
    r1 = smp_load_acquire(&x1);
    synchronize_rcu();
    WRITE_ONCE(x2, 1);
  } ||| {
    rcu_read_lock();
    r2 = READ_ONCE(x2);
    WRITE_ONCE(x0, 1);
    rcu_read_unlock();
  } }-};
  assert(!(r1 == 1 && t2_r2 == 1 && t0_r2 == 1));
  return r1 + 2 * (t2_r2 + 2 * t0_r2);
}
