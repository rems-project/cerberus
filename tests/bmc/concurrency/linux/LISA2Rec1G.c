#include "linux.h"
int main() {
  int x0, x1, x2, x3;
  int r1, r2, r3;
  {-{ {
    rcu_read_lock();
    r2 = READ_ONCE(x0);
    smp_mb();
    WRITE_ONCE(x1, 1);
    WRITE_ONCE(x2, 1);
    rcu_read_unlock();
  } ||| {
    r1 = READ_ONCE(x1);
    synchronize_rcu();
    WRITE_ONCE(x3, 1);
    r3 = READ_ONCE(x2);
  } ||| {
    rcu_read_lock();
    r2 = READ_ONCE(x3);
    WRITE_ONCE(x0, 1);
    rcu_read_unlock();
  } }-};
  assert(!((r1 == 1 && r2 == 1 && r2 == 1) || (r1 == 1 && r3 == 0)));
  return r1 + 2 * (r2 + 2 * r3);
}
