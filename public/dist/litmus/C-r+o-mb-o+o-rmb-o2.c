#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;
int T0_r2;

{-{
{ WRITE_ONCE(y,2);
smp_mb();
T0_r2 = READ_ONCE(x); }
|||
{ WRITE_ONCE(x,1);
smp_rmb();
WRITE_ONCE(y,1); }
}-};
 __BMC_ASSUME (y == 2 && T0_r2 == 0);
}
