#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;
int T0_r1;
int T1_r3;
{-{
{ T0_r1 = READ_ONCE(x);
smp_mb();
WRITE_ONCE(y,1); }
|||
{ T1_r3 = READ_ONCE(y);
smp_rmb();
WRITE_ONCE(x,1); }
}-};
 __BMC_ASSUME (T0_r1 == 1 && T1_r3 == 1);
}
