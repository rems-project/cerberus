#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;

int T1_r1;
int T1_r2;
{-{
{ WRITE_ONCE(y,1);
smp_rmb();
WRITE_ONCE(x,1); }
|||
{ T1_r1 = READ_ONCE(x);
smp_mb();
T1_r2 = READ_ONCE(y); }
}-};
 __BMC_ASSUME (T1_r1 == 1 && T1_r2 == 0);
}
