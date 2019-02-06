// LISA1Rr1G
// https://github.com/paulmckrcu/litmus/blob/master/manual/rcu/LISA1Rr1G.litmus
#include "linux.h"
int main() {
  int x0 = 0, x1 = 0, x2 = 0;
  int r1, r2;
  {-{ {
    rcu_read_lock();
    WRITE_ONCE(x0, 1);
    WRITE_ONCE(x1, 1);
    rcu_read_unlock();
    rcu_read_lock();
    WRITE_ONCE(x2, 1);
    rcu_read_unlock();
  } ||| {
    r1 = READ_ONCE(x1);
    synchronize_rcu();
    r2 = READ_ONCE(x0);
  } }-};
  assert (!(r1 == 1 && r2 == 0));
  return r1 + 2 * r2;
}
