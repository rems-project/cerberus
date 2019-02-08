#include "linux.h"
int main(void) {
int x = 0, y = 0;
int T1_r3, T2_r1, T2_r2;
{-{ {
  WRITE_ONCE(y,1);
} ||| {
  T1_r3 = READ_ONCE(y);
  smp_mb();
  WRITE_ONCE(x,1);
} ||| {
  T2_r1 = READ_ONCE(x);
  smp_rmb();
  T2_r2 = READ_ONCE(y);
  } }-};
  // Herd says this is forbidden
  // the text description says 'allowed'
  assert(!(T1_r3 == 1 && T2_r1 == 1 && T2_r2 == 0));
}
