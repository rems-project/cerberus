// This test checks that the "comparison to 0" when converting a floating type
// to _Bool is done at the **floating** type.
#include <stdio.h>
static _Bool ret(double d) { return d; }
static _Bool arg(_Bool b) { return b; }
int main(void)
{
  double half = 0.5, mhalf = -0.5, tiny = 1e-300, huge = 1e300, mzero = -0.0, zero = 0.0;
  float f = 0.25f; long double ld = 0.125L;
  _Bool decl = half;
  _Bool cast = (_Bool)mhalf;
  _Bool assign; assign = tiny;
  _Bool comp = 0; comp += huge; // _Bool += double: usual arithmetic then back to _Bool
  _Bool arr[2] = { f, ld };
  _Bool cond = zero ? 0 : half;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
         ret(half), decl, cast, assign, comp, arg(half), arr[0], arr[1], cond,
         ret(f), ret(ld), ret(mzero), ret(zero), (_Bool)huge, (_Bool)0.0);
  return 0;
}
