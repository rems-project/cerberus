// LISA2Rftx1GM
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA2Rftx1GM.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0, x3 = 0;
  int r0, r1, r2, r3;
  {-{ {
    rcu_read_lock();
    WRITE_ONCE(x1, 1);
    smp_mb();
    WRITE_ONCE(x0, 1);
    rcu_read_unlock();
    rcu_read_lock();
    WRITE_ONCE(x3, 1);
    WRITE_ONCE(x2, 1);
    rcu_read_unlock();
  | ||| {
    r0 = READ_ONCE(x0);
    synchronize_rcu();
    r3 = READ_ONCE(x3);
  } ||| {
    r2 = READ_ONCE(x2);
    smp_mb();
    r1 = READ_ONCE(x1);
  | }-}
  assert(!(r0 == 1 && r3 == 0 && r2 == 1 && r1 == 0));
  return r0 + 2 * (r3 + 2 * (r2 + 2 * r1));
}
