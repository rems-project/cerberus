#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;
int T0_r2;
int T1_r4;
{-{
{ WRITE_ONCE(x,1);
smp_mb();
T0_r2 = READ_ONCE(y); }
|||
{ WRITE_ONCE(y,1);
smp_mb();
T1_r4 = READ_ONCE(x); }
}-};
 __BMC_ASSUME (T0_r2 == 0 && T1_r4 == 0);
}
