#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;
int T0_r1;
int T0_r2;
int T1_r3;
int T1_r4;


{-{
{ T0_r1 = READ_ONCE(x);
smp_mb();
T0_r2 = READ_ONCE(y); }
|||
{ T1_r3 = READ_ONCE(y);
smp_rmb();
T1_r4 = READ_ONCE(x); }
|||
{ WRITE_ONCE(x,1); }
|||
{ WRITE_ONCE(y,1); }
}-};
 __BMC_ASSUME (T0_r1 == 1 && T0_r2 == 0 && T1_r3 == 1 && T1_r4 == 0);
}
